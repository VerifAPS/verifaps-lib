##
# Geteta Examples
#
# @file
# @version 0.1

.EXPORT_ALL_VARIABLES:


NUXMV := $(HOME)/share/nuXmv-1.1.1-Linux/bin/nuXmv
LANG := C

REPO_DIR := $(shell readlink -f ../../)
BIN_DIR := $(REPO_DIR)/exec/build/install/exec/bin/
RETETA :=  $(BIN_DIR)/reteta
GETETA := $(BIN_DIR)/geteta

ifeq ($(DEBUG),1)
	GETETA_DEBUG := --print-automaton
	RETETA_DEBUG := --print-augmented-programs --print-automaton
else
	GETETA_DEBUG :=	
endif

GETETA_FAIL := --row-map  --cexout

prepare:
	cd $(REPO_DIR) && gradle :exec:installDist --parallel

$(GETETA): prepare
$(RETETA): prepare

## concreteprogram
constantprogram_concrete: $(GETETA)
	cd constantprogram && $(GETETA) $(GETETA_DEBUG) -t constantprogram_concrete.gtt -c constantprogram.st

constantprogram: $(GETETA)
	cd constantprogram && $(GETETA) $(GETETA_DEBUG) -t constantprogram.gtt -c constantprogram.st

constantprogram_broken: $(GETETA)
	cd constantprogram && $(GETETA) $(GETETA_DEBUG) $(GETETA_FAIL)   -t constantprogram_broken.gtt -c constantprogram.st
##


## Counter
Counter: $(RETETA)
	echo TODO
##

coverage: $(GETETA)

##
cycles: $(GETETA)
	$(GETETA) $(GETETA_DEBUG) -t cycles.gtt -c cycles.st

cycles_wrong: $(GETETA)
	$(GETETA) $(GETETA_DEBUG) $(GETETA_FAIL) -t cycles_wrong.gtt -c cycles.st
##
detwait: $(GETETA)
	cd detwait && $(GETETA) $(GETETA_DEBUG) -t detwait.gtt -c detwait.st

enum: $(GETETA)

history: $(GETETA)

##
LinRe: $(GETETA)
	cd LinRe && $(GETETA) $(GETETA_DEBUG) --table lr.gtt -c lr.st
##

##
MeshedGTT: $(GETETA)


##
MinMax: $(GETETA)
	cd MinMax && $(GETETA) $(GETETA_DEBUG) -t MinMax.gtt -c MinMax.st

MinMax_broken:
	cd MinMax && $(GETETA) $(GETETA_DEBUG) -t MinMaxBroken.gtt -c MinMax.st
##


monex: $(GETETA)

## RTT
RTT_Counter: $(RETETA)
	cd RTT_Counter && $(RETETA) $(RETETA_DEBUG) \
		-t table.tt.txt -P OneCnt.st -P TwoCnt.st

RTT_emergency: $(RETETA)
	cd RTT_emergency && $(RETETA) $(RETETA_DEBUG) \
		-t emerg.gtt -P PPU_13.st -P PPU_13+ESystem.st -P ESystem@ESystem.st

RTT_if_13: $(RETETA)
	cd RTT_if &&  $(RETETA) $(RETETA_DEBUG) \
		-t emerg.gtt -P PPU_13.st -P PPU_13+ESystem.st -P ESystem@ESystem.st

RTT_if_5: $(RETETA)
	cd RTT_if &&  $(RETETA) $(RETETA_DEBUG) \
		-t emerg.gtt -P PPU_13.st -P PPU_13+ESystem.st -P ESystem@ESystem.st

RTT_if_5_noif: $(RETETA)
	cd RTT_if &&  $(RETETA) $(RETETA_DEBUG) \
		-t emerg.gtt -P PPU_13.st -P PPU_13+ESystem.st -P ESystem@ESystem.st


RTT_restart: $(RETETA)
	cd RTT_restart && $(RETETA) $(RETETA_DEBUG) \
		-t restart.gtt -P Crane@Crane_13.st -P Crane@Crane_13.st

RTT_rvdv: $(RETETA)
	cd RTT_rvdv && $(RETETA) $(RETETA_DEBUG) \
		-t rvdv.gtt -L Preamble.st -P Crane3@Code_3.st -P Crane5@Code_5.st
# end
