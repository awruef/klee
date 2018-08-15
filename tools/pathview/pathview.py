#!/usr/bin/env python2
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO
import argparse
import sys

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
    print s
    for c in conjs:
      q = c.substitute(s).simplify()
      if reads_names(q, ["stdin"]):
        #print "Pre: {}".format(c.serialize(threshold=50))
        print "{}".format(q.serialize(threshold=50))
  return 0

if __name__ == '__main__':
  parser = argparse.ArgumentParser('pathview')
  parser.add_argument('pathcond')
  args = parser.parse_args()
  sys.exit(main(args))
