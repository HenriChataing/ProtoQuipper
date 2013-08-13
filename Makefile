INCLUDE =
HDK_INCLUDE = $(INCLUDE:%=--optghc=%)
HADDOCK := haddock

BUILD_DIR = _build

GHC = ghc --make -odir $(BUILD_DIR) -hidir $(BUILD_DIR) $(INCLUDE)
HAPPY = happy --ghc --info
ALEX = alex

MAIN = ProtoQuipper

PRE_GENERATED_MODULES = Parsing/Parser.y Parsing/ConstraintParser.y Parsing/IParser.y Parsing/Lexer.x
GENERATED_MODULES = Parsing/ConstraintParser.hs Parsing/IParser.hs	\
  Parsing/Lexer.hs Parsing/Parser.hs
SOURCE_MODULES = Classes.hs Builtins.hs Interactive.hs Interpret/Circuits.hs		\
  Interpret/Interpret.hs Interpret/Values.hs Monad/Modules.hs Interpret/IRExport.hs		\
  Monad/Namespace.hs Monad/QpState.hs Monad/QuipperError.hs		\
  Console.hs Options.hs Parsing/Localizing.hs Parsing/Printer.hs			\
  Console.hs Parsing/Syntax.hs ProtoQuipper.hs Typing/CorePrinter.hs			\
  Typing/CoreSyntax.hs Typing/Driver.hs Typing/Ordering.hs		\
  Typing/Subtyping.hs Typing/TransSyntax.hs Typing/TypeInference.hs	\
  Typing/TypingContext.hs Utils.hs
MODULES = $(GENERATED_MODULES) $(SOURCE_MODULES)

SUBDIRS = Interpret Monad Typing Parsing

all : $(MODULES)
	$(GHC) -cpp $(INCLUDE) $(MAIN).hs -o $(MAIN)

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
	$(HADDOCK) -o haddock-doc -h $(HDK_INCLUDE) $(MAIN) --source-entity=src/%{MODULE/.//}.html#line-%L --source-module=src/%{MODULE/.//}.html -t "The Proto-Quipper Language" -p "prologue.txt"

haddock-html-sources : $(MODULES:%.hs=haddock-doc/src/%.html)

haddock-doc/src/%.html: %.hs
	mkdir -p "$(dir $@)"
	cat "$<" | HsColour -anchor -html > "$@"

# ----------------------------------------------------------------------
# Building documentation without source code links.

haddock-tmp : $(MODULES)
	$(HADDOCK) -o haddock-doc -h $(HDK_INCLUDE) $(MAIN)

# ----------------------------------------------------------------------
# Distribution


VERSION = 0.1
DISTDIR = proto-quipper-$(VERSION)
DISTZIP = $(DISTDIR).zip
DISTTAR = $(DISTDIR).tgz

MAKEFILES_DIST = Makefile
MAKEFILES_PUBLIC = $(MAKEFILEs_DIST:%=%-public)

QLIB_MODULES = qlib/core.qp qlib/qft.qp qlib/list.qp qlib/gates.qp
QLIB = qlib

# The README, Makefile, etc used for distribution are not the same as
# the analogous files used by developers.
PUBLIC = README COPYRIGHT
#            LICENSE

$(DISTZIP) $(DISTTAR): dist

RIGHT_COPY = maintainer/right_copy

.PHONY: dist
dist: $(PUBLIC) $(MAKEFILES_PUBLIC)
	rm -rf "$(DISTDIR)"
	mkdir "$(DISTDIR)"
	mkdir "$(DISTDIR)/$(QLIB)"
	for i in $(SUBDIRS); do mkdir "$(DISTDIR)/$$i" || exit 1; done
	for i in $(SOURCE_MODULES) $(PRE_GENERATED_MODULES) $(QLIB_MODULES); do $(RIGHT_COPY) "$$i" "$(DISTDIR)/$$i" || exit 1; done
	for i in $(MAKEFILES_DIST); do $(RIGHT_COPY) "$$i" "$(DISTDIR)/$$i" || exit 1; done
	cp -r haddock-doc/ "$(DISTDIR)/haddock-doc/"
	for i in $(PUBLIC); do $(RIGHT_COPY) "$$i" "$(DISTDIR)/" || exit 1; done
	rm -f "$(DISTZIP)"
	zip -r "$(DISTZIP)" "$(DISTDIR)"
	tar -zcf "$(DISTTAR)" "$(DISTDIR)"
