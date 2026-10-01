"""Sortie A1's syntax extensions for tools/congr.py.

The extended syntax -- restricted class abstractions, finite sums and
products, `-u`, `~P`, decimal numerals, and the atomic-wff-first parse that
keeps a parenthesised class from being read as `( ph op ps )` -- is part of
tools/congr.py, together with the congruence lemmas for those nodes
(`rabbidv`, `sumeq2dv`, `prodeq2dv`, `negeqd`, `pweqd`, ...).  This module
re-exports it, so a generator that imports it for the side effect keeps
working unchanged.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from congr import *                                   # noqa: F401,F403
from congr import Node, LOWVAR, Parser, congr         # noqa: F401
