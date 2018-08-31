#!/usr/bin/env python2
from pysmt.smtlib.parser import SmtLibParser
from pysmt.operators import op_to_str
from six.moves import cStringIO
from multiprocessing import Pool
import argparse
import copy
import sys

class FNodeVisitor(object):

  def visit(self, f):
    visited = set()
    self._visit(f, visited) 
    return

  def _visit(self, f, visited):
    if f not in visited:
      visited.add(f)
    else:
      return

    c = True
    if f.is_equals():
      c = self.visit_equals(f)
    elif f.is_not():
      c = self.visit_not(f)
    elif f.is_bv_constant():
      c = self.visit_bv_constant(f)
    elif f.is_bv_extract():
      c = self.visit_bv_extract(f)
    elif f.is_bv_concat():
      c = self.visit_bv_concat(f)
    elif f.is_bv_zext():
      c = self.visit_bv_zext(f)
    elif f.is_select():
      c = self.visit_select(f)
    elif f.is_symbol():
      c = self.visit_symbol(f)
    elif f.is_bv_urem():
      c = self.visit_bv_urem(f)
    elif f.is_bv_srem():
      c = self.visit_bv_srem(f)
    elif f.is_bv_mul():
      c = self.visit_bv_mul(f)
    elif f.is_bv_add():
      c = self.visit_bv_add(f)
    elif f.is_bv_sext():
      c = self.visit_bv_sext(f)
    elif f.is_bv_slt():
      c = self.visit_bv_slt(f)
    elif f.is_bv_ult():
      c = self.visit_bv_ult(f)
    elif f.is_bv_sle():
      c = self.visit_bv_sle(f)
    elif f.is_bv_ashr():
      c = self.visit_bv_ashr(f)
    elif f.is_bv_lshl():
      c = self.visit_bv_lshl(f)
    elif f.is_bv_lshr():
      c = self.visit_bv_lshr(f)
    elif f.is_bv_ule():
      c = self.visit_bv_ule(f)
    elif f.is_bv_and():
      c = self.visit_bv_and(f)
    elif f.is_bv_or():
      c = self.visit_bv_or(f)
    elif f.is_bv_udiv():
      c = self.visit_bv_udiv(f)
    elif f.is_bv_sub():
      c = self.visit_bv_sub(f)
    elif f.is_bv_sdiv():
      c = self.visit_bv_sdiv(f)
    elif f.is_ite():
      c = self.visit_ite(f)
    else:
      print op_to_str(f.node_type())
      raise NotImplementedError

    if c == True:
      for i in f.args():
        self._visit(i, visited)
    
    return    

  def visit_ite(self, f):
    return True

  def visit_bv_udiv(self, f):
    return True

  def visit_bv_sdiv(self, f):
    return True

  def visit_bv_sub(self, f):
    return True 
 
  def visit_bv_or(self, f):
    return True

  def visit_bv_and(self, f):
    return True

  def visit_bv_ule(self, f):
    return True

  def visit_bv_lshr(self, f):
    return True

  def visit_bv_lshl(self, f):
    return True

  def visit_bv_ashr(self, f):
    return True

  def visit_bv_sle(self, f):
    return True

  def visit_bv_ult(self, f):
    return True

  def visit_bv_slt(self, f):
    return True

  def visit_bv_sext(self, f):
    return True

  def visit_bv_add(self, f):
    return True

  def visit_bv_mul(self, f):
    return True

  def visit_bv_urem(self, f):
    return True

  def visit_bv_srem(self, f):
    return True

  def visit_symbol(self, f):
    return True

  def visit_select(self, f):
    return True

  def visit_bv_zext(self, f):
    return True

  def visit_bv_constant(self, f):
    return True

  def visit_equals(self, f):
    return True

  def visit_not(self, f):
    return True

  def visit_bv_concat(self, f):
    return True

  def visit_bv_extract(self, f):
    return True

def remove_casts(c):
  if c.is_bv_extract():
    b = c.args()[0]
    if b.is_bv_zext():
      return b.args()[0]
  return c

class FNodeToIntVisitor(FNodeVisitor):
  def __init__(self):
    self.result = None
  
  def getInt(self):
    return self.result

  def visit_bv_constant(self, c):
    assert self.result == None
    self.result = c.constant_value()

class IndexVisitor(FNodeVisitor):
  def __init__(self, s):
    self.s = s 

  def getIndices(self):
    return self.s
 
  def visit_select(self, select):
    name,index = select.args()
    v = FNodeToIntVisitor()
    v.visit(index)
    idx = v.getInt()
    self.s.add(idx)

class FNodeReplaceArrayCasts(FNodeVisitor):
  class FNodeGetExt(FNodeVisitor):
    def __init__(self, s):
      self.subs = s

    def getSubs(self):
      return self.subs

    def _visit_gen(self, e):
      base = e.args()[0]
      if base.is_array_op():
        v = IndexVisitor(set())
        v.visit(base)
        q = v.getIndices()
        if len(q) == 1:
          self.subs[e] = base
          return False
        else:
          return True
      else:
        return True

    def visit_bv_zext(self, e):
      return self._visit_gen(e)

    def visit_bv_sext(self, e):
      return self._visit_gen(e)

  def __init__(self):
    self.results = {}
  
  def visit_bv_extract(self, e):
    q = {}
    uvv = self.FNodeGetExt(q)
    uvv.visit(e)
    if len(q.keys()) == 1:
      k = q.keys()[0]
      self.results[e] = q[k]
    return False

  def getSubs(self):
    return self.results

def find_subs(cnjs, names):
  subs = []
  # Phase 1
  s1 = {}
  for c in cnjs:
    if c.is_equals():
      lhs,rhs = c.args()
      rhs_c = remove_casts(rhs)
      if rhs_c.is_array_op():
        name,idx = rhs_c.args()
        if str(name) in names:
          s1[rhs_c] = lhs
  subs.append(s1) 
  # Phase 2
  s2 = {}
  for c in cnjs:
      acv = FNodeReplaceArrayCasts()
      acv.visit(c)
      ns = acv.getSubs()
      for k in ns.keys():
        if k not in s1.keys() and k not in s2.keys():
          s2[k] = ns[k]
  subs.append(s2) 
  return subs

def reads_names(f, names):
  r = False
  if f.is_array_op():
    name = f.args()[0]
    if str(name) in names:
      r = True
  else:
    for i in f.args():
      r = r or reads_names(i, names)
  return r

def get_conjuncts(cnjs):
  v = []
  q = []
  if cnjs.is_and():
    for c in cnjs.args():
      if c.is_and():
        q.append(c)
      else:
        v.append(c)
  else:
    v.append(cnjs)

  while len(q) > 0:
    cur = q.pop()
    if cur.is_and():
      for c in cur.args():
        if c.is_and():
          q.append(c)
        else:
          v.append(c)
    else:
      v.append(cur)

  return v

def get_referred_indexes(conjs, names):
  m = {}
  for c in conjs:
    ci = c
    if reads_names(ci, names):
      idxes = set()
      v = IndexVisitor(idxes)
      v.visit(ci)
      for i in v.getIndices():
        u = m.get(i, [])
        u.append(ci)
        m[i] = u
  
  return m

def main(args):
  with open(args.pathcond, 'r') as inp:
    parser = SmtLibParser()
    b = inp.read()
    s = parser.get_script(cStringIO(b))
    conjs = []
    for cmd in s:
      if cmd.name == "assert":
        for c in cmd.args:
          conjs.extend(get_conjuncts(c.simplify()))

    subs = find_subs(conjs, ["stdin", "const_arr1"])
    stdin_conjs = copy.deepcopy(conjs)
    for s in subs:
      new_stdin_conjs = []
      for c in stdin_conjs:
        a = c.substitute(s)
        q = a.simplify()
        if reads_names(q, ["stdin"]):
          new_stdin_conjs.append(q)
      stdin_conjs = new_stdin_conjs
    stdin_idxes = get_referred_indexes(stdin_conjs, ["stdin"]) 
    ks = stdin_idxes.keys()
    ks.sort()
    for k in ks:
      print "{idx} => ( {csts} )".format(idx=k, csts=" /\\ ".join([c.serialize(threshold=50) for c in stdin_idxes[k]]))
      print ""
  return 0

if __name__ == '__main__':
  parser = argparse.ArgumentParser('pathview')
  parser.add_argument('pathcond')
  args = parser.parse_args()
  sys.exit(main(args))
