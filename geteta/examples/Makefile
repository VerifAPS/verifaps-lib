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
TTPRINT := $(BIN_DIR)/ttprint
GETETA_SMT := $(BIN_DIR)/geteta-smt
ELDARICA := $(HOME)/work/eldarica/eld
#TIME := /usr/bin/time -a -o "time.txt"

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
$(TTPRINT): prepare


## concreteprogram
constantprogram_concrete: $(GETETA)
	cd constantprogram && $(GETETA) $(GETETA_DEBUG) -t constantprogram_concrete.gtt -c constantprogram.st

constantprogram: $(GETETA)
	cd constantprogram && $(GETETA) $(GETETA_DEBUG) -t constantprogram.gtt -c constantprogram.st

constantprogram_broken: $(GETETA)
	cd constantprogram && $(GETETA) $(GETETA_DEBUG) $(GETETA_FAIL)   -t constantprogram_broken.gtt -c constantprogram.st

constantprogram-smt: $(GETETA_SMT)
	cd constantprogram && $(GETETA_SMT) -t constantprogram.gtt -c constantprogram.st
	cd constantprogram && $(ELDARICA) Ta.hcc

constantprogram_broken-smt: $(GETETA_SMT)
	cd constantprogram && $(GETETA_SMT) -t constantprogram_broken.gtt -c constantprogram.st

##


## Counter
#Counter: $(RETETA)
#	echo TODO

OneIncrement: $(GETETA)
	cd Counter && $(GETETA) $(GETETA_DEBUG) -t OneIncrement.gtt -c OneIncrement.st

OneIncrement-smt: $(GETETA_SMT)
	cd Counter && $(GETETA_SMT) -t OneIncrement.gtt -c OneIncrement.st
	cd Counter && $(ELDARICA) OneIncrement.hcc
##

coverage: $(GETETA)

##
cycles: $(GETETA)
	cd cycles && $(GETETA) $(GETETA_DEBUG) -t cycles.gtt -c cycles.st

cycles_wrong: $(GETETA)
	cd cycles && $(GETETA) $(GETETA_DEBUG) $(GETETA_FAIL) -t cycles_wrong.gtt -c cycles.st

cycles-smt: $(GETETA_SMT)
	cd cycles && $(GETETA_SMT) -t cycles.gtt -c cycles.st
	cd cycles && $(ELDARICA) TTable.hcc

cycles_wrong-smt: $(GETETA_SMT)
	cd cycles && $(GETETA_SMT) -t cycles_wrong.gtt -c cycles.st
	cd cycles && $(ELDARICA) CyclesWrong.hcc
##


detwait: $(GETETA)
	cd detwait && $(GETETA) $(GETETA_DEBUG) -t detwait.gtt -c detwait.st

enum: $(GETETA)
	cd enum && $(GETETA) $(GETETA_DEBUG) -t enum.gtt -c enum.st

history: $(GETETA)
	cd history && $(GETETA) $(GETETA_DEBUG) -t history.gtt -c history.st

history_concrete: $(GETETA)
	cd history && $(GETETA) $(GETETA_DEBUG) -t history_concrete.gtt -c history.st

##
LinRe: $(GETETA)
	cd LinRe && $(GETETA) $(GETETA_DEBUG) --table lr.gtt -c lr.st
##

##
MeshedGTT: $(GETETA)


##
MinMax-smt: $(GETETA)
	cd MinMax && $(GETETA_SMT) -t MinMax.gtt -c MinMax.st
	cd MinMax && $(ELDARICA) MinMaxTbl.hcc

MinMax: $(GETETA)
	cd MinMax && $(GETETA) $(GETETA_DEBUG) -t MinMax.gtt -c MinMax.st

MinMax_broken:
	cd MinMax && $(GETETA) $(GETETA_DEBUG) -t MinMax_Broken.gtt -c MinMax.st
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


print: $(TTPRINT)
	cd LinRe && $(TTPRINT) $(TTPRINT_OPTIONS) *.gtt
	cd MinMax && $(TTPRINT) $(TTPRINT_OPTIONS) *.gtt
	cd RTT_restart && $(TTPRINT) $(TTPRINT_OPTIONS) *.gtt
	cd RTT_rvdv && $(TTPRINT) $(TTPRINT_OPTIONS) *.gtt
	cd RTT_if && $(TTPRINT) $(TTPRINT_OPTIONS) *.gtt
	cd RTT_emergency && $(TTPRINT) $(TTPRINT_OPTIONS) *.gtt
	cd constantprogram && $(TTPRINT) $(TTPRINT_OPTIONS) *.gtt
	cd monex && $(TTPRINT) $(TTPRINT_OPTIONS) *.gtt

# end
