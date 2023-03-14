all:
	happy -gca ParCPP.y
	alex -g LexCPP.x
	ghc --make TestCPP.hs -o TestCPP
	ghc --make lab3.hs -o lab3
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocCPP.* LexCPP.* ParCPP.* LayoutCPP.* SkelCPP.* PrintCPP.* TestCPP.* AbsCPP.* TestCPP ErrM.* SharedString.* ComposOp.* CPP.dtd XMLCPP.* Makefile*
	

