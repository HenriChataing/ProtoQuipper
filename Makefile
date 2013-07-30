INCLUDE = -iparsing -iinterpret -ityping -iexport -itypingtest -imonad
HDK_INCLUDE = $(INCLUDE:%=--optghc=%)

BUILD_DIR = _build

GHC = ghc --make -odir $(BUILD_DIR) -hidir $(BUILD_DIR) $(INCLUDE)
HAPPY = happy --ghc --info
ALEX = alex

MAIN = Quipper

all : Parser.hs ConstraintParser.hs IParser.hs Lexer.hs
	$(GHC) $(INCLUDE) $(MAIN).hs -o $(MAIN)

Parser.hs :
	if [ -e _build/Parser.y ] && diff parsing/Parser.y _build/Parser.y > /dev/null ; then \
	echo "Ignoring Parser.y" ; \
	else \
	$(HAPPY) parsing/Parser.y ; \
	cp parsing/Parser.y _build/ ; \
	fi
ConstraintParser.hs :
	if [ -e _build/ConstraintParser.y ] && diff parsing/ConstraintParser.y _build/ConstraintParser.y > /dev/null ; then \
	echo "Ignoring ConstraintParser.y" ; \
	else \
	$(HAPPY) parsing/ConstraintParser.y ; \
	cp parsing/ConstraintParser.y _build/ ; \
	fi
IParser.hs :
	if [ -e _build/IParser.y ] && diff parsing/IParser.y _build/IParser.y > /dev/null ; then \
	echo "Ignoring IParser.y" ; \
	else \
	$(HAPPY) parsing/IParser.y ; \
	cp parsing/IParser.y _build/ ; \
	fi

Lexer.hs :
	if [ -e _build/Lexer.x ] && diff parsing/Lexer.x _build/Lexer.x > /dev/null ; then \
	echo "Ignoring Lexer.x" ; \
	else \
	$(ALEX) parsing/Lexer.x ; \
	cp parsing/Lexer.x _build/ ; \
	fi
clean :
	rm parsing/Parser.hs parsing/Lexer.hs parsing/ConstraintParser.hs parsing/IParser.hs
	rm _build/*

distclean : clean
	rm $(MAIN)

test : all
	for file in test/*.qi; \
	do ./$(MAIN) -i -t $$file; \
	done

count : clean
	wc -l *.hs */*.hs parsing/Lexer.x parsing/Parser.y parsing/IParser.y parsing/ConstraintParser.y

haddock : Parser.hs ConstraintParser.hs IParser.hs Lexer.hs
	./haddock-doc/haddock -o haddock-doc -h $(HDK_INCLUDE) $(MAIN) --source-entity=src/%{MODULE/.//}.html#line-%L --source-module=src/%{MODULE/.//}.html
  

