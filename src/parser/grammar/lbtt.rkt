;;; This is part of mc3, a model checking solver.
;;;
;;; Copyright (c) 2021, National Technology & Engineering Solutions of Sandia,
;;; LLC (NTESS).  Under the terms of Contract DE-NA0003525 with NTESS, the
;;; U.S. Government retains certain rights in this software.
;;;
;;; mc3 is free software: you can redistribute it and/or modify it under the
;;; terms of the GNU Lesser General Public License as published by the Free
;;; Software Foundation, either version 3 of the License, or (at your option)
;;; any later version.
;;;
;;; mc3 is distributed in the hope that it will be useful, but WITHOUT ANY
;;; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
;;; FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License for
;;; more details.
;;;
;;; You should have received a copy of the GNU Lesser General Public License
;;; along with mc3.  If not, see <https://www.gnu.org/licenses/>.


#lang brag


;;; This is a grammar for the LBTT (LTL-to-Büchi Translator Testbench) format
;;; for representing Büchi automata, as produced by Spot
;;; (https://spot.lrde.epita.fr/concepts.html#lbtt); refer to
;;; http://www.tcs.hut.fi/Software/maria/tools/lbt/ for a description of the
;;; format.


gba: NATURAL-NUMBER ; number of states
     NATURAL-NUMBER ; number of acceptance sets (if 0, all states are accepting)
     state*

state: NATURAL-NUMBER is-initial acceptance-sets /NEGATIVE-ONE transition* /NEGATIVE-ONE

is-initial: NATURAL-NUMBER ; really 0 or 1

acceptance-sets: NATURAL-NUMBER* ; there should only be one (BA, not GBA)

transition: NATURAL-NUMBER label ; [TODO: labeled transitions]

@label: TRUE | atom | negation | disjunction | conjunction

atom: IDENTIFIER

negation: /NOT label

disjunction: /OR label label

conjunction: /AND label label
