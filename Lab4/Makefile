all:
	bnfc HSK.cf
	happy -gca ParHSK.y
	alex -g LexHSK.x
	ghc --make lab4.hs -o lab4

clean:
	-rm -f lab4
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocCPP.ps

distclean: clean
	-rm -f DocHSK.* LexHSK.* ParHSK.* LayoutHSK.* SkelHSK.* PrintHSK.* TestHSK.* AbsHSK.* TestHSK ErrM.* SharedString.* ComposOp.* HSK.dtd XMLHSK.* Makefile*
