INCLUDE =
HDK_INCLUDE = $(INCLUDE:%=--optghc=%)
HADDOCK := haddock

BUILD_DIR = _build

GHC_OPTS:=-O2 -fwarn-incomplete-patterns -fwarn-incomplete-uni-patterns -Werror
GHC_PROF:= -prof -auto

GHC = ghc $(GHC_OPTS) $(GHC_PROF) --make -odir $(BUILD_DIR) -hidir $(BUILD_DIR) $(INCLUDE)
HAPPY = happy --ghc --info
ALEX = alex

MAIN = ProtoQuipper

PRE_GENERATED_MODULES = Parsing/Parser.y Parsing/Lexer.x
GENERATED_MODULES = Parsing/Lexer.hs Parsing/Parser.hs
SOURCE_MODULES = Builtins.hs Classes.hs Console.hs Interactive.hs	Driver.hs \
  Interpreter/Circuits.hs Interpreter/Interpreter.hs Interpreter/IRExport.hs	\
  Interpreter/Values.hs Core/Namespace.hs		\
  Monad/Core.hs Monad/Error.hs Monad/Typer.hs Monad/Interpreter.hs Monad/Compiler.hs \
  Options.hs \
  Parsing/Location.hs Parsing/Printer.hs Parsing/Syntax.hs		\
  ProtoQuipper.hs Core/Printer.hs Core/Syntax.hs Core/Translate.hs Core/Environment.hs	\
  Typing/Ordering.hs Typing/Subtyping.hs Typing/TypeInference.hs	\
  Typing/TypingContext.hs Utils.hs \
  Compiler/PatternElimination.hs Compiler/SimplSyntax.hs Compiler/Circuits.hs \
  Compiler/Continuations.hs Compiler/LlvmExport.hs
MODULES = $(GENERATED_MODULES) $(SOURCE_MODULES)

all: $(MAIN)

$(MAIN): $(MODULES)
	$(GHC) $(INCLUDE) $(MAIN).hs -o $(MAIN)

Parsing/Parser.hs: Parsing/Parser.y
	$(HAPPY) Parsing/Parser.y

Parsing/Lexer.hs: Parsing/Lexer.x
	$(ALEX) Parsing/Lexer.x

clean:
	rm -f $(GENERATED_MODULES)
	rm -f $(GENERATED_MODULES:%.hs=%.info)
	rm -f $(MAIN) $(MAIN).exe $(MAIN).prof $(MAIN).aux
	rm -rf $(BUILD_DIR)/*

count: clean
	wc -l *.hs */*.hs Parsing/Lexer.x Parsing/Parser.y foreign/*

# ----------------------------------------------------------------------
# Building documentation with source code links. This requires a
# patched version of Haddock, as well as HsColour.

.PHONY: doc
doc haddock : haddock-documentation haddock-html-sources

haddock-documentation : $(MODULES)
	$(HADDOCK) -o doc -h $(HDK_INCLUDE) $(MAIN) --source-entity=src/%{MODULE/.//}.html#line-%L --source-module=src/%{MODULE/.//}.html -t "The Proto-Quipper Language" -p "prologue.txt"

haddock-html-sources : $(MODULES:%.hs=doc/src/%.html) doc/src/Main.html

doc/src/%.html: %.hs
	mkdir -p "$(dir $@)"
	cat "$<" | HsColour -anchor -html > "$@"

doc/src/Main.html: ProtoQuipper.hs
	mkdir -p "$(dir $@)"
	cat "$<" | HsColour -anchor -html > "$@"

doc-clean haddock-clean :
	rm -rf doc

# ----------------------------------------------------------------------
# Building documentation without source code links.

haddock-simple : $(MODULES)
	$(HADDOCK) -o doc -h $(HDK_INCLUDE) $(MAIN)

# ----------------------------------------------------------------------
# Distribution


VERSION = 0.2.1
DISTDIR = proto-quipper-$(VERSION)
DISTZIP = $(DISTDIR).zip
DISTTAR = $(DISTDIR).tgz

MAKEFILES_DIST = Makefile

QP_MODULES = qlib/core.qp qlib/function.qp qlib/qft.qp qlib/list.qp	\
 qlib/gates.qp bwt/definitions.qp bwt/bwt.qp bwt/definitions_imp.qp	\
 bwt/bwt_imp.qp

OTHER_DIST = emacs/proto-quipper-mode.el

PUBLIC = README COPYRIGHT prologue.txt NEWS
#            LICENSE

$(DISTZIP) $(DISTTAR): dist

RIGHT_COPY = maintainer/right_copy

.PHONY: dist
dist: $(PUBLIC) $(MAKEFILES_DIST) $(SOURCE_MODULES) $(PRE_GENERATED_MODULES) $(QP_MODULES) $(OTHER_DIST) $(RIGHT_COPY)
	rm -rf "$(DISTDIR)"
	mkdir "$(DISTDIR)"
	mkdir "$(DISTDIR)/$(BUILD_DIR)"
	for i in $(MAKEFILES_DIST) $(SOURCE_MODULES) $(PRE_GENERATED_MODULES) $(QP_MODULES) $(OTHER_DIST); do mkdir -p "$(DISTDIR)/`dirname "$$i"`" && $(RIGHT_COPY) "$$i" "$(DISTDIR)/$$i" || exit 1; done
	for i in $(PUBLIC); do $(RIGHT_COPY) "$$i" "$(DISTDIR)/" || exit 1; done
	cd "$(DISTDIR)"; make doc
	cd "$(DISTDIR)"; make clean
	rm -f "$(DISTZIP)"
	zip -r "$(DISTZIP)" "$(DISTDIR)"
	tar -zcf "$(DISTTAR)" "$(DISTDIR)"


distcheck: $(DISTZIP)
	rm -rf "$(DISTDIR)"
	rm -rf "$(DISTDIR)-orig"
	unzip "$(DISTZIP)"
	cp -rp "$(DISTDIR)" "$(DISTDIR)-orig"
	cd "$(DISTDIR)"; $(MAKE) all
	cd "$(DISTDIR)"; $(MAKE) bwt.circ
	cd "$(DISTDIR)"; $(MAKE) clean
	diff -rq "$(DISTDIR)-orig" "$(DISTDIR)" || (echo "Some files were not cleaned" >& 2 ; exit 1)
	cd "$(DISTDIR)-orig"; $(MAKE) doc
	rm -rf "$(DISTDIR)-orig"
	@echo "$(DISTZIP) seems ready for distribution."

distclean:
	rm -rf $(DISTDIR)
	rm -f $(DISTTAR)
	rm -f $(DISTZIP)

# ----------------------------------------------------------------------
# Spell-checking

spellcheck: haddock-documentation
	ispell -d american -p ./dictionary.txt -H doc/*.html
