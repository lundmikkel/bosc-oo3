/* File ListC/listmachine.c
   A unified-stack abstract machine and garbage collector
   for list-C, a variant of micro-C with cons cells.
   sestoft@itu.dk * 2009-11-17, 2012-02-08

   Compile like this, on ssh.itu.dk say:
      gcc -Wall listmachine.c -o listmachine

   If necessary, force compiler to use 32 bit integers:
      gcc -m32 -Wall listmachine.c -o listmachine

   To execute a program file using this abstract machine, do:
      ./listmachine <programfile> <arg1> <arg2> ...
   To get also a trace of the program execution:
      ./listmachine -trace <programfile> <arg1> <arg2> ...

   This code assumes -- and checks -- that values of type
   int, unsigned int and unsigned int* have size 32 bits.
*/

/*
   Data representation in the stack s[...] and the heap:
    * All integers are tagged with a 1 bit in the least significant
      position, regardless of whether they represent program integers,
      return addresses, array base addresses or old base pointers
      (into the stack).
    * All heap references are word-aligned, that is, the two least
      significant bits of a heap reference are 00.
    * Integer constants and code addresses in the program array
      p[...] are not tagged.
   The distinction between integers and references is necessary for
   the garbage collector to be precise (not conservative).

   The heap consists of 32-bit words, and the heap is divided into
   blocks.  A block has a one-word header block[0] followed by the
   block's contents: zero or more words block[i], i=1..n.

   A header has the form ttttttttnnnnnnnnnnnnnnnnnnnnnngg
   where tttttttt is the block tag, all 0 for cons cells
     nn....nn is the block length (excluding header)
     gg       is the block's color

   The block color has this meaning:
   gg=00=White: block is dead, not reachable from the stack (after mark, before sweep)
   gg=01=Grey:  block is live, children not marked (during mark)
   gg=10=Black: block is live, reachable from the stack (after mark, before sweep)
   gg=11=Blue:  block is on the freelist or orphaned

   A block of length zero is an orphan; it cannot be used
   for data and cannot be on the freelist.  An orphan is
   created when allocating all but the last word of a free block.
*/

#define Exercise_10_2 2
#define Exercise_10_3 3
#define Exercise_10_4 4
#define Exercise_10_5 5

// Change to constants above to switch between exercises
int Exercise = Exercise_10_5;


#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>

typedef unsigned int word;

#define IsInt(v)			(((v)  & 1) == 1)
#define Tag(v)  			(((v) << 1) | 1)
#define Untag(v)			( (v) >> 1)

#define isReference(w)		!IsInt(w) && w != 0

#define White 0				// block is dead, not reachable from the stack (after mark, before sweep)
#define Grey  1				// block is live, children not marked (during mark)
#define Black 2				// block is live, reachable from the stack (after mark, before sweep)
#define Blue  3				// block is on the freelist or orphaned

#define isWhite(hdr)		Color(hdr) == White
#define isGrey(hdr) 		Color(hdr) == Grey
#define isBlack(hdr)		Color(hdr) == Black
#define isBlue(hdr) 		Color(hdr) == Blue

#define BlockTag(hdr)		((hdr)>>24)						// Shift 24 bits to get tttttttt
#define Length(hdr)			(((hdr)>>2)&0x003FFFFF)			// Shift 2 bits to remove garbage and use logical and to get the 22 next bits (all the n's)
#define Color(hdr)			((hdr)&3)						// Logical and with 3 (11) to get the first two bits
#define Paint(hdr, color)   hdr = (((hdr)&(~3))|(color))	// Logical and of negative 3 (00) to remove color and the use logical or to set the color

#define isOrphan(w)		Length(w) <= 0

#define CONSTAG 0

// Heap size in words

#define HEAPSIZE 1000

word* heap;
word* afterHeap;
word* freelist;

// These numeric instruction codes must agree with ListC/Machine.fs:
// (Use #define because const int does not define a constant in C)

#define CSTI     0
#define ADD      1
#define SUB      2
#define MUL      3
#define DIV      4
#define MOD      5
#define EQ       6
#define LT       7
#define NOT      8
#define DUP      9
#define SWAP    10
#define LDI     11
#define STI     12
#define GETBP   13
#define GETSP   14
#define INCSP   15
#define GOTO    16
#define IFZERO  17
#define IFNZRO  18
#define CALL    19
#define TCALL   20
#define RET     21
#define PRINTI  22
#define PRINTC  23
#define LDARGS  24
#define STOP    25
#define NIL     26
#define CONS    27
#define CAR     28
#define CDR     29
#define SETCAR  30
#define SETCDR  31

#define STACKSIZE 1000

// Print the stack machine instruction at p[pc]

void printInstruction(int p[], int pc)
{
    switch (p[pc])
    {
    case CSTI:   printf("CSTI %d", p[pc + 1]); break;
    case ADD:    printf("ADD"); break;
    case SUB:    printf("SUB"); break;
    case MUL:    printf("MUL"); break;
    case DIV:    printf("DIV"); break;
    case MOD:    printf("MOD"); break;
    case EQ:     printf("EQ"); break;
    case LT:     printf("LT"); break;
    case NOT:    printf("NOT"); break;
    case DUP:    printf("DUP"); break;
    case SWAP:   printf("SWAP"); break;
    case LDI:    printf("LDI"); break;
    case STI:    printf("STI"); break;
    case GETBP:  printf("GETBP"); break;
    case GETSP:  printf("GETSP"); break;
    case INCSP:  printf("INCSP %d", p[pc + 1]); break;
    case GOTO:   printf("GOTO %d", p[pc + 1]); break;
    case IFZERO: printf("IFZERO %d", p[pc + 1]); break;
    case IFNZRO: printf("IFNZRO %d", p[pc + 1]); break;
    case CALL:   printf("CALL %d %d", p[pc + 1], p[pc + 2]); break;
    case TCALL:  printf("TCALL %d %d %d", p[pc + 1], p[pc + 2], p[pc + 3]); break;
    case RET:    printf("RET %d", p[pc + 1]); break;
    case PRINTI: printf("PRINTI"); break;
    case PRINTC: printf("PRINTC"); break;
    case LDARGS: printf("LDARGS"); break;
    case STOP:   printf("STOP"); break;
    case NIL:    printf("NIL"); break;
    case CONS:   printf("CONS"); break;
    case CAR:    printf("CAR"); break;
    case CDR:    printf("CDR"); break;
    case SETCAR: printf("SETCAR"); break;
    case SETCDR: printf("SETCDR"); break;
    default:     printf("<unknown>"); break;
    }
}

// Print current stack (marking heap references by #) and current instruction

void printStackAndPc(int s[], int bp, int sp, int p[], int pc)
{
    printf("[ ");
    int i;
    for (i = 0; i <= sp; i++)
        if (IsInt(s[i]))
            printf("%d ", Untag(s[i]));
        else
            printf("#%d ", s[i]);
    printf("]");
    printf("{%d:", pc); printInstruction(p, pc); printf("}\n");
}

// Read instructions from a file, return array of instructions

int* readfile(char* filename)
{
    int capacity = 1, size = 0;
    int* program = (int*)malloc(sizeof(int) * capacity);
    FILE* inp = fopen(filename, "r");
    int instr;
    while (fscanf(inp, "%d", &instr) == 1)
    {
        if (size >= capacity)
        {
            int* buffer = (int*)malloc(sizeof(int) * 2 * capacity);
            int i;
            for (i = 0; i < capacity; i++)
                buffer[i] = program[i];
            free(program);
            program = buffer;
            capacity *= 2;
        }
        program[size++] = instr;
    }
    fclose(inp);
    return program;
}

word* allocate(unsigned int tag, unsigned int length, int s[], int sp);

// The machine: execute the code starting at p[pc]

int execcode(int p[], int s[], int iargs[], int iargc, int /* boolean */ trace)
{
    int bp = -999;        // Base pointer, for local variable access
    int sp = -1;          // Stack top pointer
    int pc = 0;           // Program counter: next instruction
    for (;;)
    {
        if (trace) {
            printStackAndPc(s, bp, sp, p, pc);
        }

        switch (p[pc++])
        {
        	case CSTI:
        	    s[sp + 1] = Tag(p[pc++]); sp++; break;
        	case ADD:
        	    s[sp - 1] = Tag(Untag(s[sp - 1]) + Untag(s[sp])); sp--; break;
        	case SUB:
        	    s[sp - 1] = Tag(Untag(s[sp - 1]) - Untag(s[sp])); sp--; break;
        	case MUL:
        	    s[sp - 1] = Tag(Untag(s[sp - 1]) * Untag(s[sp])); sp--; break;
        	case DIV:
        	    s[sp - 1] = Tag(Untag(s[sp - 1]) / Untag(s[sp])); sp--; break;
        	case MOD:
        	    s[sp - 1] = Tag(Untag(s[sp - 1]) % Untag(s[sp])); sp--; break;
        	case EQ:
        	    s[sp - 1] = Tag(s[sp - 1] == s[sp] ? 1 : 0); sp--; break;
        	case LT:
        	    s[sp - 1] = Tag(s[sp - 1] < s[sp] ? 1 : 0); sp--; break;
        	case NOT:
        	{
        	    int v = s[sp];
        	    s[sp] = Tag((IsInt(v) ? Untag(v) == 0 : v == 0) ? 1 : 0);
        	} break;
        	case DUP:
        	    s[sp + 1] = s[sp]; sp++; break;
        	case SWAP:
        	{
        	    int tmp = s[sp];
        	    s[sp] = s[sp - 1];
        	    s[sp - 1] = tmp;
        	} break;
        	case LDI:                 // load indirect
        	    s[sp] = s[Untag(s[sp])]; break;
        	case STI:                 // store indirect, keep value on top
        	    s[Untag(s[sp - 1])] = s[sp]; s[sp - 1] = s[sp]; sp--; break;
        	case GETBP:
        	    s[sp + 1] = Tag(bp); sp++; break;
        	case GETSP:
        	    s[sp + 1] = Tag(sp); sp++; break;
        	case INCSP:
        	    sp = sp + p[pc++]; break;
        	case GOTO:
        	    pc = p[pc]; break;
        	case IFZERO:
        	{
        	    int v = s[sp--];
        	    pc = (IsInt(v) ? Untag(v) == 0 : v == 0) ? p[pc] : pc + 1;
        	} break;
        	case IFNZRO:
        	{
        	    int v = s[sp--];
        	    pc = (IsInt(v) ? Untag(v) != 0 : v != 0) ? p[pc] : pc + 1;
        	} break;
        	case CALL:
        	{
        	    int argc = p[pc++];
        	    int i;
        	    for (i = 0; i < argc; i++)           // Make room for return address
        	        s[sp - i + 2] = s[sp - i];         // and old base pointer
        	    s[sp - argc + 1] = Tag(pc + 1); sp++;
        	    s[sp - argc + 1] = Tag(bp);   sp++;
        	    bp = sp + 1 - argc;
        	    pc = p[pc];
        	} break;
        	case TCALL:
        	{
        	    int argc = p[pc++];                  // Number of new arguments
        	    int pop  = p[pc++];                  // Number of variables to discard
        	    int i;
        	    for (i = argc - 1; i >= 0; i--) // Discard variables
        	        s[sp - i - pop] = s[sp - i];
        	    sp = sp - pop; pc = p[pc];
        	} break;
        	case RET:
        	{
        	    int res = s[sp];
        	    sp = sp - p[pc]; bp = Untag(s[--sp]); pc = Untag(s[--sp]);
        	    s[sp] = res;
        	} break;
        	case PRINTI:
        	    printf("%d ", IsInt(s[sp]) ? Untag(s[sp]) : s[sp]); break;
        	case PRINTC:
        	    printf("%c", Untag(s[sp])); break;
        	case LDARGS:
        	{
        	    int i;
        	    for (i = 0; i < iargc; i++) // Push commandline arguments
        	        s[++sp] = Tag(iargs[i]);
        	} break;
        	case STOP:
        	    return 0;
        	case NIL:
        	    s[sp + 1] = 0; sp++; break;
        	case CONS:
        	{
        	    word* w = allocate(CONSTAG, 2, s, sp);
        	    w[1] = (word)s[sp - 1];
        	    w[2] = (word)s[sp];
        	    s[sp - 1] = (int)w;
        	    sp--;
        	} break;
        	case CAR:
        	{
        	    word* w = (word*)s[sp];
        	    if (w == 0)
        	    {
        	        printf("Cannot take car of null\n");
        	        return -1;
        	    }
        	    s[sp] = (int)(w[1]);
        	} break;
        	case CDR:
        	{
        	    word* w = (word*)s[sp];
        	    if (w == 0)
        	    {
        	        printf("Cannot take cdr of null\n");
        	        return -1;
        	    }
        	    s[sp] = (int)(w[2]);
        	} break;
        	case SETCAR:
        	{
        	    word v = (word) s[sp--];
        	    word* w = (word*) s[sp];
        	    w[1] = v;
        	} break;
        	case SETCDR:
        	{
        	    word v = (word) s[sp--];
        	    word* w = (word*) s[sp];
        	    w[2] = v;
        	} break;
        	default:
        	    printf("Illegal instruction %d at address %d\n", p[pc - 1], pc - 1);
        	    return -1;
        }
    }
}

// Read program from file, and execute it

int execute(int argc, char** argv, int /* boolean */ trace)
{
    int* p = readfile(argv[trace ? 2 : 1]);         // program bytecodes: int[]
    int* s = (int*)malloc(sizeof(int) * STACKSIZE); // stack: int[]
    int iargc = trace ? argc - 3 : argc - 2;
    int* iargs = (int*)malloc(sizeof(int) * iargc); // program inputs: int[]
    int i;
    for (i = 0; i < iargc; i++)                     // Convert commandline arguments
        iargs[i] = atoi(argv[trace ? i + 3 : i + 2]);
    // Measure cpu time for executing the program
    struct rusage ru1, ru2;
    getrusage(RUSAGE_SELF, &ru1);
    int res = execcode(p, s, iargs, iargc, trace);  // Execute program proper
    getrusage(RUSAGE_SELF, &ru2);
    struct timeval t1 = ru1.ru_utime, t2 = ru2.ru_utime;
    double runtime = t2.tv_sec - t1.tv_sec + (t2.tv_usec - t1.tv_usec) / 1000000.0;
    printf("\nUsed %7.3f cpu seconds\n", runtime);
    return res;
}

// Garbage collection and heap allocation

word mkheader(unsigned int tag, unsigned int length, unsigned int color)
{
    return (tag << 24) | (length << 2) | (color << 0);
}

int inHeap(word* p)
{
    return heap <= p && p < afterHeap;
}

// Call this after a GC to get heap statistics:

void heapStatistics()
{
    int blocks		= 0,
    	free		= 0,
    	orphans		= 0,
        blocksSize	= 0,
        freeSize	= 0,
        largestFree = 0;
    word* heapPtr = heap;

    while (heapPtr < afterHeap)
    {
        if (Length(heapPtr[0]) > 0)
        {
            blocks++;
            blocksSize += Length(heapPtr[0]);
        }
        else
            orphans++;

        word* nextBlock = heapPtr + Length(heapPtr[0]) + 1;
        if (nextBlock > afterHeap)
        {
            printf("HEAP ERROR: block at heap[%d] extends beyond heap\n",
                   heapPtr - heap);
            exit(-1);
        }
        heapPtr = nextBlock;
    }
    word* freePtr = freelist;
    while (freePtr != 0)
    {
        free++;
        int length = Length(freePtr[0]);
        if (freePtr < heap || afterHeap < freePtr + length + 1)
        {
            printf("HEAP ERROR: freelist item %d (at heap[%d], length %d) is outside heap\n",
                   free, freePtr - heap, length);
            exit(-1);
        }
        freeSize += length;
        largestFree = length > largestFree ? length : largestFree;
        if (Color(freePtr[0]) != Blue)
            printf("Non-blue block at heap[%d] on freelist\n", (int)freePtr);
        freePtr = (word*) freePtr[1];
    }
    printf("Heap: %d blocks (%d words); of which %d free (%d words, largest %d words); %d orphans\n",
           blocks, blocksSize, free, freeSize, largestFree, orphans);
}

void initheap()
{
    heap = (word*) malloc(sizeof(word) * HEAPSIZE);
    afterHeap = &heap[HEAPSIZE];
    // Initially, entire heap is one block on the freelist:
    heap[0] = mkheader(0, HEAPSIZE - 1, Blue);
    heap[1] = (word)0;
    freelist = &heap[0];
}

void mark(word* block) {
	// Find white blocks
    if (isWhite(block[0]))
    {
        // Paint black
        Paint(block[0], Black);

	    // Recursively mark all references
	    for (int i = 1; i <= Length(block[0]); ++i)
	    {
	    	if (isReference(block[i])) {
	    		mark((word*) block[i]);
	    	}
	    }
    }
}


void markGrey(word* block) {
    // Paint black
    Paint(block[0], Black);

    // Recursively mark all references
    for (int i = 1; i <= Length(block[0]); ++i)
    {
    	if (isReference(block[i]) && isWhite(block[i])) {
		    Paint(block[i], Grey);
    	}
    }
}

void markPhase(int s[], int sp)
{
	printf("marking ...\n");

    // Exercise 10.2
	if (Exercise < Exercise_10_5)
	{
	    // Loop through stack
	    for (int i = 0; i <= sp; ++i)
	    {
	    	// Mark all references
	    	if (isReference(s[i])) {
	    		mark((word*) s[i]);
	    	}
	    }
	}

	// Exercise 10.5
	else {
		// Loop through stack to find heap elements that are directly reacable
	    for (int i = 0; i <= sp; ++i)
	    {
	    	if (isReference(s[i]) && isWhite(s[i]))
		    {
		        // Paint grey
		        Paint(s[i], Grey);
	    	}
	    }

	    // Loop through heap repeatedly until no grey cells are found
	    int foundGrey;
	    do {
	    	foundGrey = 0;
	    	word* block;
		    for (int i = 0; i < HEAPSIZE; i += 1 + Length(block[0]))
		    {
		    	block = (word*) &heap[i];

		    	// Find white blocks
			    if (isReference(block[0]) && isGrey(block[0]))
			    {
			    	markGrey(block);
			    	foundGrey = 0;
			    }
		    }
		} while (foundGrey);
	}
}

void sweepPhase()
{
    printf("sweeping...\n");

    word* block;
    
    // Loop through all elements on the heap
    for (int i = 0; i < HEAPSIZE; i += 1 + Length(block[0]))
    {
    	// TODO: Check if BlockTag is 0, else go to next element?

    	// Get element from heap
    	block = (word*) &heap[i];

    	// Paint black blocks white again
    	if (isBlack(block[0])) {
    		Paint(block[0], White);
    	}
    	// Put white blocks on the freelist
    	else if (isWhite(block[0])) {
    		// Paint blue
    		Paint(block[0], Blue);


    		// Exercise 10.3
    		if (Exercise == Exercise_10_3)
    		{
    			int offset = Length(block[0]) + 1;

	    		// Is there a next block and is it white?
    			if (i + offset < HEAPSIZE && isWhite(block[offset])) {
					int new_length = offset + Length(block[offset]);

    				// Create new header for block
    				block[0] = mkheader(CONSTAG, new_length, Blue);
	    		}
	    	}

	    	// Exercise 10.4
	    	else if (Exercise == Exercise_10_4)
    		{
    			int tryAgain;
    			do {
    				tryAgain = 0;
	    			int offset = Length(block[0]) + 1;

		    		// Is there a next block and is it white?
	    			if (i + offset < HEAPSIZE && isWhite(block[offset])) {
						int new_length = offset + Length(block[offset]);

	    				// Create new header for block
	    				block[0] = mkheader(CONSTAG, new_length, Blue);
	    				tryAgain = 1;
		    		}
		    	} while (tryAgain);
	    	}

    		// Don't add orphans to freelist as they can't point to the next element
    		if (!isOrphan(block[0])) {
    			// Point second element to next free element
    			block[1] = (word) freelist;
    			freelist = (word*) &block[0];
    		}
    	}
    }
}

void collect(int s[], int sp)
{
	printf("\nGarbage collecting\n");

    markPhase(s, sp);
    //heapStatistics();
    sweepPhase();
    //heapStatistics();
}

word* allocate(unsigned int tag, unsigned int length, int s[], int sp)
{
    int attempt = 1;
    do
    {
        word* free = freelist;
        word** prev = &freelist;
        while (free != 0)
        {
            int rest = Length(free[0]) - length;
            if (rest >= 0)
            {
                if (rest == 0) // Exact fit with free block
                    *prev = (word*) free[1];
                else if (rest == 1)   // Create orphan (unusable) block
                {
                    *prev = (word*) free[1];
                    free[length + 1] = mkheader(0, rest - 1, Blue);
                }
                else     // Make previous free block point to rest of this block
                {
                    *prev = &free[length + 1];
                    free[length + 1] = mkheader(0, rest - 1, Blue);
                    free[length + 2] = free[1];
                }
                free[0] = mkheader(tag, length, White);
                return free;
            }
            prev = (word**) &free[1];
            free = (word*) free[1];
        }
        // No free space, do a garbage collection and try again
        if (attempt == 1)
            collect(s, sp);
    }
    while (attempt++ == 1);
    printf("Out of memory\n");
    exit(1);
}

// Read code from file and execute it

int main(int argc, char** argv)
{
    if (sizeof(word) != 4 || sizeof(word*) != 4 || sizeof(int) != 4)
    {
        printf("Size of word, word* or int is not 32 bit, cannot run\n");
        return -1;
    }
    else if (argc < 2)
    {
        printf("Usage: listmachine [-trace] <programfile> <arg1> ...\n");
        return -1;
    }
    else
    {
        int trace = argc >= 3 && 0 == strncmp(argv[1], "-trace", 7);
        initheap();
        return execute(argc, argv, trace);
    }
}
