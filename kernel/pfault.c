/* This file contains code for a generic page fault handler for processes. */
#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "elf.h"

#include "sleeplock.h"
#include "fs.h"
#include "buf.h"

int loadseg(pagetable_t pagetable, uint64 va, struct inode *ip, uint offset, uint sz);
int flags2perm(int flags);

/* CSE 536: (2.4) read current time. */
uint64 read_current_timestamp() {
  uint64 curticks = 0;
  acquire(&tickslock);
  curticks = ticks;
  wakeup(&ticks);
  release(&tickslock);
  return curticks;
}

bool psa_tracker[PSASIZE];

/* All blocks are free during initialization. */
void init_psa_regions(void)
{
    for (int i = 0; i < PSASIZE; i++) 
        psa_tracker[i] = false;
}

/* Evict heap page to disk when resident pages exceed limit */
void evict_page_to_disk(struct proc* p) {
    /* Find free block */
    // printf("lavdeeee");
    int startBlock = 0;
    for (int i = 0; i < PSASIZE; i++) {
        if (!psa_tracker[i]) {
            startBlock = i;
            break;
        }
    }
    for (int i = startBlock; i < startBlock + 4; i++) {
        psa_tracker[i] = true;
    }

    // printf("Evicted block %d\n", startBlock);
    /* Find victim page using FIFO. */
    int evict_pageTime =__INT_MAX__;
    int max_time_heap_page_index = 0;

    for (int i = 0; i < MAXHEAP; i++) {
        if (p->heap_tracker[i].loaded == 1 && (p->heap_tracker[i].last_load_time < evict_pageTime)){//p->heap_tracker[max_time_heap_page_index].last_load_time)) {
            max_time_heap_page_index = i;
            evict_pageTime = p->heap_tracker[i].last_load_time;
        }
    }
    // printf("evict indxxxxxx : %d\n", max_time_heap_page_index);
    p->heap_tracker[max_time_heap_page_index].loaded = false;
    p->heap_tracker[max_time_heap_page_index].startblock = startBlock;
    
    /* Print statement. */
    uint64 va = p->heap_tracker[max_time_heap_page_index].addr;
    print_evict_page(va, startBlock);
    /* Read memory from the user to kernel memory first. */
    char* kpage = kalloc();
    if (kpage == 0) {
        return;
    }
    // memset(kpage, 0, PGSIZE);
    // int vpn = PGROUNDDOWN((uint64) va) >> PGSHIFT;
    // copyin(p->pagetable, kpage, va, PGSIZE)
    if (copyin(p->pagetable, kpage, va, PGSIZE) != 0) {
        //printf("copy page to kernel memory fail");
    }
    
    /* Write to the disk blocks. Below is a template as to how this works. There is
     * definitely a better way but this works for now. :p */
    // p->heap_tracker[max_time_heap_page_index].startblock = PSASTART+(blockno);

    // struct buf* b;
    // char *ptr = kpage;
    // for (int k=blockno; k < blockno + 4; k++) {
    //     b = bread(1, PSASTART+(blockno));
    //     memmove(b->data, ptr, PGSIZE/4);
    //     ptr += PGSIZE/4;
    //     bwrite(b);
    //     brelse(b);
    // }

    for (int i = 0; i < 4; i++) {
        struct buf* b = bread(1, PSASTART + (startBlock + i));
        memmove(b->data, kpage + (i * BSIZE), BSIZE);
        bwrite(b);
        brelse(b);
    }
    kfree(kpage);

    /* Unmap swapped out page */
    uvmunmap(p->pagetable, PGROUNDDOWN(va), 1, 0);
    /* Update the resident heap tracker. */
    p->resident_heap_pages -= 1;
}

/* Retrieve faulted page from disk. */
void retrieve_page_from_disk(struct proc* p, uint64 uvaddr) {
    /* Find where the page is located in disk */
    int startBlock = 0;
    int heap_index = -1;
    
    for (int i = 0; i < MAXHEAP; i++) {
        if (p->heap_tracker[i].loaded) {
            continue;
        }
        if (p->heap_tracker[i].addr <= uvaddr && uvaddr < p->heap_tracker[i].addr+PGSIZE) {
            startBlock = p->heap_tracker[i].startblock;
            heap_index = i;
            break;
        }
    }


    /* Print statement. */
    print_retrieve_page(uvaddr, startBlock);

    /* Create a kernel page to read memory temporarily into first. */
    char* kpage = kalloc();
    if (kpage == 0) {
        return;
    }
    /* Read the disk block into temp kernel page. */

    // for(int k=startBlock; k < startBlock + 4; k++) {
    //     b = bread(1, k);
    //     ptr = b->data;
    //     ptr += PGSIZE/4;
    // }

    for (int i = 0; i < 4; i++) {
        struct buf* b = bread(1, PSASTART + (startBlock + i));
        memmove(kpage + (i * BSIZE), b->data, BSIZE);
        brelse(b);
    }
    for (int i = startBlock; i < startBlock + 4; i++) {
        psa_tracker[i] = false;
    }
    /* Copy from temp kernel page to uvaddr (use copyout) */
    if (copyout(p->pagetable,  p->heap_tracker[heap_index].addr, kpage, PGSIZE) != 0) {
        //printf("copy page from kernel memory fail");
    }
    kfree(kpage);

    p->heap_tracker[heap_index].startblock = -1;
}


void page_fault_handler(void) 
{
    /* Current process struct */
    struct proc *p = myproc();
    char* path;
    path = p->name;
    int i, off;
    struct elfhdr elf;
    struct inode* ip;
    struct proghdr ph;
    pagetable_t pagetable = 0;

    /* Track whether the heap page should be brought back from disk or not. */
    bool load_from_disk = false;

    /* Find faulting address. */
    uint64 faulting_address = r_stval();
    uint64 faulting_address_base;
    //printf("%x", faulting_address);
    faulting_address_base = faulting_address >> 12;
    faulting_address_base = faulting_address_base << 12;
    //printf("%x", faulting_address_base);
    print_page_fault(p->name, faulting_address_base);

    /* Check if the fault address is a heap page. Use p->heap_tracker */
    int heap_index = -1;
    for (int i = 0; i < MAXHEAP; i++) {
        if (p->heap_tracker[i].addr <= faulting_address_base && faulting_address_base < p->heap_tracker[i].addr + PGSIZE) {
            heap_index = i;
            break;
        }
    }
    // printf("indexxxxxxxx %d \n", heap_index);
    if (heap_index != -1) {
        goto heap_handle;
    }
    //if (p->heap_tracker->loaded) {
    //    goto heap_handle;
    //}
    

    

    /* If it came here, it is a page from the program binary that we must load. */
    ip = namei(path);
    ilock(ip);
    readi(ip, 0, (uint64)&elf, 0, sizeof(elf));
    pagetable = p->pagetable;
    


    for (i = 0, off = elf.phoff; i < elf.phnum; i++, off += sizeof(ph)) {
        if(readi(ip, 0, (uint64)&ph, off, sizeof(ph)) != sizeof(ph))
            goto bad;
        if(ph.type != ELF_PROG_LOAD)
        {
            continue;
        }
        if(ph.memsz < ph.filesz)
            goto bad;
        if(ph.vaddr + ph.memsz < ph.vaddr)
            goto bad;
        if(ph.vaddr % PGSIZE != 0)
            goto bad;

        uint64 addr = 0;
        if(ph.vaddr + ph.memsz - faulting_address_base >= PGSIZE) {
            addr = PGSIZE;
        } else {
            addr = ph.vaddr + ph.memsz - faulting_address_base;
        }


        if ( ph.vaddr <= faulting_address_base && faulting_address_base < (ph.vaddr + ph.memsz))
        {
            uvmalloc(pagetable, faulting_address_base, faulting_address_base + addr, flags2perm(ph.flags));

            loadseg(pagetable, faulting_address_base, ip, ph.off + faulting_address_base - ph.vaddr, addr);

            print_load_seg(faulting_address_base, ph.off, ph.filesz);
            break;
        }
        print_skip_section(p->name, ph.vaddr, ph.memsz);
    }

    
    p->pagetable = pagetable;

    iunlockput(ip);
    
    
    /* Go to out, since the remainder of this code is for the heap. */
    goto out;



heap_handle:
    /* 2.4: Check if resident pages are more than heap pages. If yes, evict. */
    // printf("p sz : %d,  fault  %x   page   %x    disk %d   total size %d index  %d \n", p->sz, faulting_addr, page, load_from_disk, p->resident_heap_pages);
    // printf("heap  indexxx %d \n", heap_index);
    if (p->resident_heap_pages == MAXRESHEAP) {
        evict_page_to_disk(p);
    }

    /* 2.3: Map a heap page into the process' address space. (Hint: check growproc) */
    if (uvmalloc(p->pagetable, faulting_address_base, faulting_address_base + PGSIZE, PTE_W) == 0) {
        panic("Errorwith new page");
    }

    /* 2.4: Update the last load time for the loaded heap page in p->heap_tracker. */
    p->heap_tracker[heap_index].last_load_time = read_current_timestamp();

    /* 2.4: Heap page was swapped to disk previously. We must load it from disk. */
    if (p->heap_tracker[heap_index].startblock != -1) {
        retrieve_page_from_disk(p, faulting_address_base);
    }

    /* Track that another heap page has been brought into memory. */
    p->heap_tracker[heap_index].loaded = true;
    p->resident_heap_pages++;



out:
    /* Flush stale page table entries. This is important to always do. */
    sfence_vma();
    return;

bad:
    if(ip){
        iunlockput(ip);
        end_op();
    }
    return;

}
