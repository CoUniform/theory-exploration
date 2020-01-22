all:
	ghc -o theory_exp Main.hs

clean:
	rm *.o *.hi theory_exp
