INCLUDE = -iparsing

BUILD_DIR = _build

GHC = ghc --make -odir $(BUILD_DIR) -hidir $(BUILD_DIR) $(INCLUDE)
HAPPY = happy --ghc
ALEX = alex

MAIN = Quipper

all : Parser.hs Lexer.hs
	$(GHC) $(INCLUDE) $(MAIN).hs -o $(MAIN)

Parser.hs :
	$(HAPPY) parsing/Parser.y
Lexer.hs :
	$(ALEX) parsing/Lexer.x

clean :
	rm parsing/Parser.hs parsing/Lexer.hs
	rm _build/*

distclean : clean
	rm $(MAIN)

test : all
	for file in test/*.qi; \
	do ./$(MAIN) -i -t $$file; \
	done
