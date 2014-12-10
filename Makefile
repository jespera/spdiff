# Copyright 2005-2009, Ecole des Mines de Nantes, University of Copenhagen
# Yoann Padioleau, Julia Lawall, Rene Rydhof Hansen, Henrik Stuart, Gilles Muller, Jesper Andersen
# This file is part of Coccinelle.
# 
# Coccinelle is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, according to version 2 of the License.
# 
# Coccinelle is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License
# along with Coccinelle.  If not, see <http://www.gnu.org/licenses/>.
# 
# The authors reserve the right to distribute this or future versions of
# Coccinelle under other licenses.


##############################################################################
# Variables
##############################################################################
TARGET=spdiff

SRC=ANSITerminal.ml \
		hashcons.ml \
		jconfig.ml \
		gtree.ml \
		env.ml \
		gtree_util.ml \
		util.ml \
		genericparser.ml \
		genericlexer.ml \
		difftype.ml \
		visitor_j.ml \
		control_flow_c2.ml \
		ast_to_flow2.ml \
	 	msa.ml \
		diff.ml \
		reader.ml \
		main.ml

COCCI=coccinelle
SYSDIR=/usr/lib/ocaml

SYSLIBS=str.cma unix.cma bigarray.cma 
LIBS=$(COCCI)/commons/commons.cma $(COCCI)/globals/globals.cma $(COCCI)/parsing_c/parsing_c.cma 
#LIBS=$(COCCI)/commons/commons.cma $(COCCI)/globals/globals.cma $(COCCI)/parsing_c/parsing_c.cma $(COCCI)/parsing_c/pretty_print_c.cmx hashcons.cmx db.cmx gtree.cmx difftype.cmx visitor_j.cmx ast_to_flow2.cmx diff.cmx main.cmx
#LIBS=$(COCCI)/commons/commons.cma $(COCCI)/globals/globals.cma $(COCCI)/parsing_c/parsing_c.cma $(COCCI)/parsing_c/pretty_print_c.cmo hashcons.cmo db.cmo gtree.cmo difftype.cmo visitor_j.cmo diff.cmo main.cmo

MAKESUBDIRS=$(COCCI)/commons $(COCCI)/globals $(COCCI)/parsing_cocci $(COCCI)/parsing_c
INCLUDEDIRS=$(COCCI)/commons $(COCCI)/commons/ocamlextra $(COCCI)/globals $(COCCI)/commons/ocollection $(COCCI)/globals $(COCCI)/parsing_c 

##############################################################################
# Generic variables
##############################################################################

INCLUDES=$(INCLUDEDIRS:%=-I %)

OBJS=    $(SRC:.ml=.cmo)
OPTOBJS= $(SRC:.ml=.cmx)

EXEC=$(TARGET)

##############################################################################
# Generic ocaml variables
##############################################################################

OCAMLCFLAGS=-g -dtypes -custom -annot # -w A

# for profiling add  -p -inline 0
# but 'make forprofiling' below does that for you.
# This flag is also used in subdirectories so don't change its name here.
OPTFLAGS=-g -dtypes

# the OPTBIN variable is here to allow to use ocamlc.opt instead of 
# ocaml, when it is available, which speeds up compilation. So
# if you want the fast version of the ocaml chain tools, set this var 
# or setenv it to ".opt" in your startup script.
OPTBIN= .opt

OCAMLC=ocamlc$(OPTBIN) $(OCAMLCFLAGS)  $(INCLUDES)
OCAMLOPT=ocamlopt$(OPTBIN) $(OPTFLAGS) $(INCLUDES) 
OCAMLLEX=ocamllex #-ml # -ml for debugging lexer, but slightly slower
OCAMLYACC=ocamlyacc -v
OCAMLDEP=ocamldep #$(INCLUDES)
OCAMLMKTOP=ocamlmktop -g -custom $(INCLUDES)


##############################################################################
# Top rules
##############################################################################

all: rec $(EXEC)
opt: rec.opt $(EXEC).opt

rec:
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i all; done 
rec.opt:
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i all.opt; done 

$(EXEC): $(LIBS) $(OBJS)
	$(OCAMLC) -o $@ $(SYSLIBS) $^

$(EXEC).opt: $(LIBS:.cma=.cmxa) $(OPTOBJS) 
#	$(OCAMLOPT) -o $@ $(SYSLIBS:.cma=.cmxa) -ccopt -static $^
	$(OCAMLOPT) -o $@ $(SYSLIBS:.cma=.cmxa)  $^

$(EXEC).top: $(LIBS) $(OBJS) 
	$(OCAMLMKTOP) -o $@ $(SYSLIBS) $^

clean::
	rm -f $(TARGET) $(TARGET).opt $(TARGET).top genericparser.mli

clean::
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i clean; done 


##############################################################################
# Developer rules
##############################################################################

test: $(TARGET)
	./$(TARGET) -testall

# -inline 0  to see all the functions in the profile.
forprofiling:
	$(MAKE) OPTFLAGS="-p -inline 0 " opt

clean::
	rm -f gmon.out 

tags:
	otags -no-mli-tags -r  .

##############################################################################
# Misc rules
##############################################################################

# each member of the project can have its own test.ml. this file is 
# not under CVS.
test.ml: 
	echo "let foo_ctl () = failwith \"there is no foo_ctl formula\"" \
	  > test.ml

beforedepend:: test.ml


#INC=$(dir $(shell which ocaml))
#INCX=$(INC:/=)
#INCY=$(dir $(INCX))
#INCZ=$(INCY:/=)/lib/ocaml
#
#prim.o: prim.c
#	gcc -c -o prim.o -I $(INCZ) prim.c


##############################################################################
# Generic ocaml rules
##############################################################################

.SUFFIXES: .ml .mli .cmo .cmi .cmx .cmxa

.ml.cmo:
	$(OCAMLC)  -c $<
.mli.cmi:
	$(OCAMLC)  -c $<
.ml.cmx:
	$(OCAMLOPT)  -c $<

%.ml: %.mll
	$(OCAMLLEX) $<

%.ml: %.mly
	menhir $<
	$(OCAMLC) -c $(<:mly=mli)

.ml.mldepend: 
	$(OCAMLC) -i $< 


clean::
	rm -f *.cm[iox] *.o *.annot

clean::
	rm -f *~ .*~ *.exe #*#

beforedepend::

depend:: beforedepend
	$(OCAMLDEP) *.mli *.ml > .depend
	set -e; for i in $(MAKESUBDIRS); do $(MAKE) -C $$i depend; done

-include .depend
# DO NOT DELETE
