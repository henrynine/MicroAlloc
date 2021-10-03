# MicroAlloc
MicroAlloc is a basic memory allocator that uses segregated fit free lists to track available memory. In addition, when blocks are freed, they're placed onto an unsorted list before eventually being coalesced and returned to the appropriate free list for their size. This increases speed at the cost of a minor increase in fragmentation. 

MicroAlloc is designed to be dynamically linked in at runtime. On Linux, this can be done with LD_PRELOAD:

    make
    LD_PRELOAD=./microalloc.so ls
    
## Next steps

These are improvements I want to make to MicroAlloc:

  * Add benchmarks to compare speed and fragmentation to other allocators for a variety of programs
  * `mmap` large requests (>= 1 MB)
  * Thread safety
  * Add quick lists and deferred coalescing to further improve speed
