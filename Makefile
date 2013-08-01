INCLUDE =
HDK_INCLUDE = $(INCLUDE:%=--optghc=%)
HADDOCK := haddock

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

Parsing/Parser.hs : Parsing/Parser.y
	$(HAPPY) Parsing/Parser.y

Parsing/ConstraintParser.hs : Parsing/ConstraintParser.y
	$(HAPPY) Parsing/ConstraintParser.y

Parsing/IParser.hs : Parsing/IParser.y
	$(HAPPY) Parsing/IParser.y

Parsing/Lexer.hs : Parsing/Lexer.x
	$(ALEX) Parsing/Lexer.x

clean :
	rm -f $(GENERATED_MODULES)
	rm -f _build/*/*
	rm -rf haddock-doc

distclean : clean
	rm -f $(MAIN)

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
	$(HADDOCK) -o haddock-doc -h $(HDK_INCLUDE) $(MAIN) --source-entity=src/%{MODULE/.//}.html#line-%L --source-module=src/%{MODULE/.//}.html

haddock-html-sources : $(MODULES:%.hs=haddock-doc/src/%.html)

haddock-doc/src/%.html: %.hs
	mkdir -p "$(dir $@)"
	cat "$<" | HsColour -anchor -html > "$@"

# ----------------------------------------------------------------------
# Building documentation without source code links.

haddock-tmp : $(MODULES)
	$(HADDOCK) -o haddock-doc -h $(HDK_INCLUDE) $(MAIN)
