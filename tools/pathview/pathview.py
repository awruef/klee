#!/usr/bin/env python2
from pysmt.smtlib.parser import SmtLibParser
from pysmt.operators import op_to_str
from six.moves import cStringIO
import argparse
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

    if f.is_equals():
      self.visit_equals(f)
    elif f.is_not():
      self.visit_not(f)
    elif f.is_bv_constant():
      self.visit_bv_constant(f)
    elif f.is_bv_extract():
      self.visit_bv_extract(f)
    elif f.is_bv_zext():
      self.visit_bv_zext(f)
    elif f.is_select():
      self.visit_select(f)
    elif f.is_symbol():
      self.visit_symbol(f)
    elif f.is_bv_srem():
      self.visit_bv_srem(f)
    elif f.is_bv_mul():
      self.visit_bv_mul(f)
    elif f.is_bv_add():
      self.visit_bv_add(f)
    elif f.is_bv_sext():
      self.visit_bv_sext(f)
    elif f.is_bv_slt():
      self.visit_bv_slt(f)
    elif f.is_bv_ult():
      self.visit_bv_ult(f)
    elif f.is_bv_sle():
      self.visit_bv_sle(f)
    else:
      print op_to_str(f.node_type())
      raise NotImplementedError
    for i in f.args():
      self._visit(i, visited)
    return    

  def visit_bv_sle(self, f):
    pass

  def visit_bv_ult(self, f):
    pass

  def visit_bv_slt(self, f):
    pass

  def visit_bv_sext(self, f):
    pass

  def visit_bv_add(self, f):
    pass

  def visit_bv_mul(self, f):
    pass

  def visit_bv_srem(self, f):
    pass

  def visit_symbol(self, f):
    pass

  def visit_select(self, f):
    pass

  def visit_bv_zext(self, f):
    pass

  def visit_bv_constant(self, f):
    pass

  def visit_equals(self, f):
    pass

  def visit_not(self, f):
    pass
 
  def visit_bv_extract(self, f):
    pass

def remove_casts(c):
  if c.is_bv_extract():
    b = c.args()[0]
    if b.is_bv_zext():
      return b.args()[0]
  return c

def find_subs(cnjs, names):
  subs = {}
  for c in cnjs:
    if c.is_equals():
      lhs,rhs = c.args()
      rhs_c = remove_casts(rhs)
      if rhs_c.is_array_op():
        name,idx = rhs_c.args()
        if str(name) in names:
          subs[rhs_c] = lhs
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

    s = find_subs(conjs, ["stdin", "const_arr1"])
    stdin_conjs = []
    for c in conjs:
      q = c.substitute(s).simplify()
      if reads_names(q, ["stdin"]):
        stdin_conjs.append(q)
    stdin_idxes = get_referred_indexes(conjs, ["stdin"]) 
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
