/* Juntao Wang
 * 4/27/2019
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss
 *  2. Instruction loads (I) are ignored
 *  3. data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus an possible eviction.
 *
 * The function printSummary() is given to print output.
 */
#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include "cachelab.h"

#define MAXFILE 256
enum Policy {LRU=0, LFU=1};

struct arguments {
  int verbose;           // Show verbose debug output to stderr (not stdout)
  int help;              // Int boolean on whether to show help/usage
  int sbits;             // Number of bits for set number
  int perset;            // Number of lines per set (E)
  int bbits;             // Number of bits for block offset
  int policy;            // Policy: 0-LRU, 1:LFU
  char tracefile[MAXFILE];  // Name of valgrind trace to replay
};

struct cachestats {
  int miss_count;
  int hit_count;
  int eviction_count;
};

// single cache line, no data storage needed
struct cLine
{
  int valid;        // 1: line is not empty
  long tag;         // tag bits of address
  long recent;      // record  for LRU
  long freq;        // record for LFU
};

/* ----------------------------------------------------------------------------
 * Purpose:
 *   Print to stderr the full set of operational arguments for the program.
 * Parameters:
 *   struct arguments * args: a pointer to the structure that will get
 *                            filled in with the argument defaults and cmd line
 * Return:
 *   None
 * ---------------------------------------------------------------------------*/
void print_args(struct arguments * args) {
  fprintf(stderr, "\nCache Simulator Arguments:\n");
  fprintf(stderr, "  verbose (v): %s\n", args->verbose ? "TRUE" : "FALSE");
  fprintf(stderr, "  help (h):    %s\n", args->help  ? "TRUE" : "FALSE");
  fprintf(stderr, "  sbits (s):   %d\n", args->sbits);
  fprintf(stderr, "  perset (E):  %d\n", args->perset);
  fprintf(stderr, "  bits (b):    %d\n", args->bbits);
  fprintf(stderr, "  policy (p):  %s\n", args->policy == 1?"LFU":"LRU");
  fprintf(stderr, "  trace (t):   %s\n",  args->tracefile);
  fprintf(stderr, "\n");
}

/*
 * print_usage - Print usage info
 */
void print_usage(char* argv[])
{
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -p <policy> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -p <num>   Policy: 0-LRU, 1-LFU.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t -p 1 traces/yi.trace\n", argv[0]);
    exit(0);
}

/* ----------------------------------------------------------------------------
 * Purpose:
 *   Process the argc and argv and fill in the global arguments structure with
 *   the operational arguments for the ICMP client program.
 * Parameters:
 *   int argc: count of arguments
 *   char **argv: vector of string pointers for command line arguments
 * Return:
 *   None
 * Other:
 *   Fills in global `cmdargs` with all parsed arguments.
 * ---------------------------------------------------------------------------*/
void process_args(int argc, char ** argv, struct arguments * args) {
  int c;

  // Start by setting up the defaults for all arguments
  args->verbose = 0;
  args->help = 0;
  args->sbits = 8;
  args->perset = 1;
  args->bbits = 8;
  args->policy = LRU;
  strcpy(args->tracefile, "traces/dave.trace");

  // Define structure that specifies what to do for long arguments
  struct option long_options[] = {
    {"verbose", no_argument,       &args->verbose,  1},
    {"help",    no_argument,       &args->help,     1},
    {"sbits",   required_argument, NULL,          's'},
    {"perset",  required_argument, NULL,          'E'},
    {"bbits",   required_argument, NULL,          'b'},
    {"policy",  required_argument, NULL,          'p'},
    {"trace",   required_argument, NULL,          't'},
    {0, 0, 0, 0}
  };

  while(1) {
    // getopt_long stores the option index here.
    int option_index = 0;

    c = getopt_long (argc, argv, "vhs:E:b:p:t:",
                     long_options, &option_index);

    /* Detect the end of the options. */
    if (c == -1)
      break;

    switch (c) {
      case 0:
        assert (long_options[option_index].flag != 0);
        break;
      case 'v':
        args->verbose = 1;
        break;
      case 'h':
        args->help = 1;
        break;
      case 's':
        assert(optarg);
        args->sbits = atoi(optarg);
        break;
      case 'E':
        assert(optarg);
        args->perset = atoi(optarg);
        break;
      case 'b':
        assert(optarg);
        args->bbits = atoi(optarg);
        break;
      case 'p':
        assert(optarg);
        args->policy = atoi(optarg);
        break;
      case 't':
        assert(optarg);
        strcpy(args->tracefile, optarg);
        break;

      case '?':
        /* getopt_long already printed an error message. */
        break;

      default:
        //print_usage(argv);
        abort ();
    }
  } // while
}

/* ----------------------------------------------------------------------------
 * Purpose:
 *   fill empty cache lines with initial values
 * Parameters:
 *   int lines: E, number of lines per set
 *   int sets: S, number of sets in a cache
 * Return:
 *   a pointer to an array of pointers to cLine structure
 * ---------------------------------------------------------------------------*/
struct cLine ** buildCache(int lines, int sets)
{
  int i; // set index
  int j; // line index
  // use a double pointer as cache
  // allocate memory for array of cLine pointers
  struct cLine ** cache = (struct cLine **) malloc(sizeof(struct cLine *) * sets);
  // initialize cache line
  struct cLine singleLine = {0,0,0,0};
  for (i = 0; i < sets; i++)
  {
    // use a cLine pointer as set
    // allocate memory for array of cLine
    struct cLine * linePtr = (struct cLine *) malloc(sizeof(struct cLine) * lines);
    for (j = 0; j<lines; j++)
    {
      // store cLine to the cLine array at j
      linePtr[j] = singleLine;
    }
    // store cLine pointer to the set array at i
    cache[i] = linePtr;
  }
  return cache;
}

/* ----------------------------------------------------------------------------
 * Purpose:
 *   compare current tag to the tag in a cache line
 * Parameters:
 *   long tag1: tag from current address
 *   long tag2: tag in each cache line
 * Return:
 *   1: same tag
 *   0: not same
 * ---------------------------------------------------------------------------*/
int sameTag(long tag1, long tag2)
{
  if (tag1 == tag2)
  {
    return 1;
  }
  return 0;
}

/* ----------------------------------------------------------------------------
 * Purpose:
 *   iterate through lines of a set, check for hit, miss, or evict
 *   find LRU or LFU index
 *   update cache stats
 * Parameters:
 *   struct cLine * singleSet: pointer to array of cache lines
 *   struct cachestats * stats: pointer to cache stats
 *   int lines: number of lines per set
 *   long tag: tag of current address
 *   long clock: record for LRU
 *   policy: LRU or LFU
 *   char result[]: result string for verbose
 * Return:
 *   None
 * ---------------------------------------------------------------------------*/
void surveySet(struct cLine * singleSet, struct cachestats * stats,
  int lines, long tag, long clock, int policy, char result[])
{
  int stored = 0;       // if 0, no hit, cache is full, need eviction
  long minLRU = clock;  // initialize min LRU/LFU count with highest value
  long minLFU = clock;
  int minLRUIndex = 0;  // record of LRU/LFU index
  int minLFUIndex = 0;
  int finalIndex = 0;   // final index for eviction
  int i = 0;            // index of line
  while(i < lines)
  {
    // set might be full, check each line
    if (singleSet[i].valid)
    {
      if (sameTag(singleSet[i].tag, tag))
      {
        // same tag, hit
        stats->hit_count += 1;
        stored = 1;                   // no need for eviction
        singleSet[i].recent = clock;  // highest value means newest
        singleSet[i].freq += 1;
        strcpy(result, "hit ");
        break;                        // no need to check other lines
      }
      if (singleSet[i].recent < minLRU)
      {
        // update the min LRU value and index
        minLRU = singleSet[i].recent;
        minLRUIndex = i;
      }
      if (singleSet[i].freq < minLFU)
      {
        // update the min LFU value and index
        minLFU = singleSet[i].freq;
        minLFUIndex = i;
      }
      else if (singleSet[i].freq == minLFU)
      {
        // there are multiple minLFU, pick the least recent one
        if (singleSet[i].recent < minLRU)
        {
          minLFUIndex = i;
        }
      }
    }
    else // set is not full
    {
      singleSet[i].valid = 1;
      singleSet[i].tag = tag;
      singleSet[i].recent = clock;
      stats->miss_count += 1;
      stored = 1;
      strcpy(result, "miss ");
      break;  // since stored, no need to check other lines
    }
    i++;
  }
  // outside while loop, all lines are checked
  // but there is no hit or miss, so the set is full, need eviction
  if (!stored)
  {
    // choose final index according to policy
    if (policy == LRU)
    {
      finalIndex = minLRUIndex;
    }
    else if (policy == LFU)
    {
      finalIndex = minLFUIndex;
    }
    singleSet[finalIndex].recent = clock;
    singleSet[finalIndex].tag = tag;
    singleSet[finalIndex].freq = 0; // reset frequency due to eviction
    stats->miss_count += 1;
    stats->eviction_count += 1;
    strcpy(result, "evict ");
  }
}

/* ----------------------------------------------------------------------------
 * Purpose:
 *   extract tag bits from an address
 * Parameters:
 *   long address: 64-bit address
 *   int sbits: set bits length
 *   int bbits: block bits length
 * Return:
 *   tag bits of the address
 * ---------------------------------------------------------------------------*/
long findTag(long address, int sbits, int bbits)
{
  int tbits = 64-sbits-bbits; // tag bits length
  long mask = ~((~0)<< tbits); // 0000000000001111 for example
  long tag = (address >> (sbits+bbits)) & mask;
  return tag;
}

/* ----------------------------------------------------------------------------
 * Purpose:
 *   extract set bits from an address
 * Parameters:
 *   long address: 64-bit address
 *   int sbits: set bits length
 *   int bbits: block bits length
 * Return:
 *   set bits of the address
 * ---------------------------------------------------------------------------*/
long findSet(long address, int sbits, int bbits)
{
  int mask = ~((~0)<< sbits);
  // set bits are in the middle, to the left of block bits
  long setNumber = (address >> bbits) & mask;
  return setNumber;
}

/* ----------------------------------------------------------------------------
 * Purpose:
 *   simulate cache
 * Parameters:
 *   struct cLine ** cache: pointer to array of cLine pointers
 *   struct cachestats * stats: pointer to cache stats
 *   long tag: tag of current address
 *   setNumber: index of set
 *   int lines: number of lines per set
 *   long clock: record for LRU, update with each operation
 *   char operation: Load, Store, Modify
 *   int policy: LRU or LFU
 *   int verbose: toggle verbose mode
 * Return:
 *   None
 * ---------------------------------------------------------------------------*/
void cacheSim(struct cLine ** cache, struct cachestats * stats, long tag,
  long setNumber, int lines, long clock, char operation, int policy, int verbose)
{
  char result[6]; // result string
  // operation I is filtered out during read file stage
  // so regardless of operation, check set at least once
  surveySet(cache[setNumber], stats, lines, tag, clock, policy, result);
  if (verbose)
  {
    printf("%s", result);
  }
  // M is treated as one L and one S, so check set one more time
  if (operation == 'M')
  {
    clock++; // addtional operation means clock increment
    surveySet(cache[setNumber], stats, lines, tag, clock, policy, result);
    if (verbose)
    {
      printf("%s", result);
    }
  }
  if (verbose)
  {
    printf("\n");
  }
}

/*
 * main - Main routine
 */
int main(int argc, char* argv[])
{
  long clock = 0; // initialize clock counter for LRU
  struct arguments args;
  struct cachestats stats = {0, 0, 0};

  process_args(argc, argv, &args);
  if (args.verbose) {
    print_args(&args);
  }
  if (args.help) {
    print_usage(argv);
    exit(0);
  }
  char readline[MAXFILE];
  char operation;             // L, S, M
  long address = 0;           // 64-bit memory address
  int bytes = 0;
  int sets = 1 << args.sbits; // S = 2 to the power of sbits
  struct cLine ** cache = buildCache(args.perset, sets); // initialize cache

  FILE * inFile;
  inFile = fopen(args.tracefile, "r");
  // check for invalid filename
  if (inFile==NULL)
  {
    fprintf(stderr,"\"%s\" does no exist.\n", args.tracefile);
    exit(1);
  }
  // read a whole line each time until EOF
  while (fgets(readline, MAXFILE, inFile) != NULL)
  {
    // ignore I and other useless data
    if (readline[0] == ' ')
    {
      clock++;
      // read line into variables
      sscanf(readline," %c %lx,%i", &operation, &address, &bytes);
      long tag = findTag(address, args.sbits, args.bbits);
      long setNumber = findSet(address, args.sbits, args.bbits);
      if (args.verbose)
      {
        printf("%c %lx,%i ", operation, address, bytes);
      }
      cacheSim(cache, &stats, tag, setNumber, args.perset, clock, operation, args.policy, args.verbose);
    }
  }
  fclose(inFile);

  // free memory
  int i;
  for (i=0;i<sets;i++)
  {
    // free each cLine pointer
    free(cache[i]);
  }
  free(cache);

  /* Output the hit and miss statistics */
  printSummary(stats.hit_count, stats.miss_count, stats.eviction_count);
  return 0;
}
