######
#
# A simple Makefile
#
######

ACC=gcc \
-std=c99 -D_XOPEN_SOURCE \
-DATS_MEMALLOC_LIBC $(INCLUDE)

# ACC=g++ \
# -fpermissive -w \
# -DATS_MEMALLOC_LIBC $(INCLUDE)

CAT=cat
RMF=rm -f

######

# set TEMPTORY to different directory
# by specifying TMP

TMP=
NONE=

ifneq ($(TMP),$(NONE))
export TEMPTORY=$(TMP)
endif

TEMPOPT= $(TEMPTORY)/bin/tempopt
TEMPACC= $(TEMPTORY)/bin/tempacc -O2

######

INCLUDE :=
INCLUDE += -I${TEMPTORY}
INCLUDE += -I${TEMPTORY}/ccomp/runtime

######

all:: dynarray_dats strbuf_dats getopt_dats slist_dats argp_dats

######

testall:: all
testall:: regress
testall:: cleanall

######

dynarray_dats: \
dynarray.dats; $(TEMPACC) -DATS_MEMALLOC_LIBC -o $@ $<
strbuf_dats: \
strbuf.dats; $(TEMPACC) -DATS_MEMALLOC_LIBC -o $@ $<
getopt_dats: \
getopt.dats; $(TEMPACC) -DATS_MEMALLOC_LIBC -o $@ $<
slist_dats: \
slist.dats; $(TEMPACC) -DATS_MEMALLOC_LIBC -o $@ $<
argp_dats: \
argp.dats; $(TEMPACC) -DATS_MEMALLOC_LIBC -o $@ $<

######

regress:: dynarray_dats; ./dynarray_dats
regress:: strbuf_dats; ./strbuf_dats
regress:: getopt_dats test_getopt.sh; ./test_getopt.sh
regress:: slist_dats test_slist.sh; ./test_slist.sh
regress:: argp_dats; ./argp_dats

######

clean:: ; $(RMF) *~
clean:: ; $(RMF) a.out
clean:: ; $(RMF) *_?ats.c

cleanall:: clean
cleanall:: ; $(RMF) *_dats

###### end of [Makefile] ######
