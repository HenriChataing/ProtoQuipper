INCLUDE =

BUILD_DIR = _build

GHC = ghc --make -odir $(BUILD_DIR) -hidir $(BUILD_DIR)
HAPPY = happy --ghc
ALEX = alex

MAIN = Quipper

all : Parser.hs Lexer.hs
	$(GHC) $(INCLUDE) $(MAIN).hs -o $(MAIN)

Parser.hs :
	$(HAPPY) Parser.y
Lexer.hs :
	$(ALEX) Lexer.x

clean :
	rm Parser.hs Lexer.hs
	rm _build/*

distclean : clean
	rm $(MAIN)

test : all
	for file in test/*.qi; \
	do ./$(MAIN) -i -t $$file; \
	done
