#!/usr/bin/env python2
import argparse
import sys

def main(args):
  return 0

if __name__ == '__main__':
  parser = argparse.ArgumentParser('pathview')
  parser.add_argument('pathcond')
  args = parser.parse_args()
  sys.exit(main(args))
