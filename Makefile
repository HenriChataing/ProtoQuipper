INCLUDE =

BUILD_DIR = _build

GHC = ghc --make -odir $(BUILD_DIR) -hidir $(BUILD_DIR)
HAPPY = happy --ghc

MAIN = Quipper

all : Parser.hs
	$(GHC) $(INCLUDE) $(MAIN).hs -o $(MAIN)

Parser.hs :
	$(HAPPY) Parser.y

clean :
	rm Parser.hs
	rm _build/*

distclean : clean
	rm $(MAIN)

