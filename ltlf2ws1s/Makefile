# Parser Makefile
# need flex bison

PARSERCFILES =	../ltllexer.c ../ltlparser.c
PARSERHFILES =	../ltllexer.h ../ltlparser.h
ALLCFILES   =	$(PARSERCFILES) ../ltl_formula.c ../trans.c ../utility.cpp ltlf2ws1s.cpp
CC	    =   g++ -std=c++11
CDEBUG	    =	-g
INCLUDE	    =   -I../

ltl2smv:	$(PARSERCFILES)

ltllexer.c:	../grammar/ltllexer.l
		flex ../grammar/ltllexer.l

ltlparser.c:	../grammar/ltlparser.y
		bison ../grammar/ltlparser.y

run:	$(ALLCFILES)
	$(CC) $(INCLUDE) $(CDEBUG) $(ALLCFILES) -o ltlf2ws1s

run_debug:  $(ALLCFILES)
	    $(CC) $(INCLUDE) $(CDEBUG) $(ALLCFILES) -o ltlf2ws1s

run_release:	run

clean:
	rm -f *.o *~ $(PARSERHFILES) $(PARSERCFILES) ltlf2ws1s

