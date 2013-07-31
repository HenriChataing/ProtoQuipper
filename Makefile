INCLUDE =
HDK_INCLUDE = $(INCLUDE:%=--optghc=%)

BUILD_DIR = _build

GHC = ghc --make -odir $(BUILD_DIR) -hidir $(BUILD_DIR) $(INCLUDE)
HAPPY = happy --ghc --info
ALEX = alex

MAIN = Quipper

GENERATED_MODULES = Parsing/ConstraintParser.hs Parsing/IParser.hs	\
  Parsing/Lexer.hs Parsing/Parser.hs
SOURCE_MODULES = Classes.hs Builtins.hs Interpret/Circuits.hs		\
  Interpret/Interpret.hs Interpret/Values.hs Monad/Modules.hs		\
  Monad/Namespace.hs Monad/QpState.hs Monad/QuipperError.hs		\
  Options.hs Parsing/Localizing.hs Parsing/Printer.hs			\
  Parsing/Syntax.hs Quipper.hs Typing/CorePrinter.hs			\
  Typing/CoreSyntax.hs Typing/Driver.hs Typing/Ordering.hs		\
  Typing/Subtyping.hs Typing/TransSyntax.hs Typing/TypeInference.hs	\
  Typing/TypingContext.hs Utils.hs
MODULES = $(GENERATED_MODULES) $(SOURCE_MODULES)

all : $(MODULES)
	$(GHC) $(INCLUDE) $(MAIN).hs -o $(MAIN)

Parsing/Parser.hs :
	if [ -e _build/Parser.y ] && diff Parsing/Parser.y _build/Parser.y > /dev/null ; then \
	echo "Ignoring Parser.y" ; \
	else \
	$(HAPPY) Parsing/Parser.y ; \
	cp Parsing/Parser.y _build/ ; \
	fi
Parsing/ConstraintParser.hs :
	if [ -e _build/ConstraintParser.y ] && diff Parsing/ConstraintParser.y _build/ConstraintParser.y > /dev/null ; then \
	echo "Ignoring ConstraintParser.y" ; \
	else \
	$(HAPPY) Parsing/ConstraintParser.y ; \
	cp Parsing/ConstraintParser.y _build/ ; \
	fi
Parsing/IParser.hs :
	if [ -e _build/IParser.y ] && diff Parsing/IParser.y _build/IParser.y > /dev/null ; then \
	echo "Ignoring IParser.y" ; \
	else \
	$(HAPPY) Parsing/IParser.y ; \
	cp Parsing/IParser.y _build/ ; \
	fi

Parsing/Lexer.hs :
	if [ -e _build/Lexer.x ] && diff Parsing/Lexer.x _build/Lexer.x > /dev/null ; then \
	echo "Ignoring Lexer.x" ; \
	else \
	$(ALEX) Parsing/Lexer.x ; \
	cp Parsing/Lexer.x _build/ ; \
	fi

clean :
	rm $(GENERATED_MODULES)
	rm _build/*/* _build/*.y _build/*.x
	rm -rf haddock-doc

distclean : clean
	rm $(MAIN)

test : all
	for file in test/*.qi; \
	do ./$(MAIN) -i -t $$file; \
	done

count : clean
	wc -l *.hs */*.hs Parsing/Lexer.x Parsing/Parser.y Parsing/IParser.y Parsing/ConstraintParser.y

# ----------------------------------------------------------------------
# Building documentation with source code links. This requires a
# patched version of Haddock, as well as HsColour.

haddock : haddock-documentation haddock-html-sources

haddock-documentation : $(MODULES)
	haddock -o haddock-doc -h $(HDK_INCLUDE) $(MAIN) --source-entity=src/%{MODULE/.//}.html#line-%L --source-module=src/%{MODULE/.//}.html

haddock-html-sources : $(MODULES:%.hs=haddock-doc/src/%.html)

haddock-doc/src/%.html: %.hs
	mkdir -p "$(dir $@)"
	cat "$<" | HsColour -anchor -html > "$@"

# ----------------------------------------------------------------------
# Building documentation without source code links.

haddock-tmp : $(MODULES)
	haddock -o haddock-doc -h $(HDK_INCLUDE) $(MAIN)
