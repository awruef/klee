//===-- SearcherTest.cpp ----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#define KLEE_UNITTEST

#include "gtest/gtest.h"

#include "Core/ExecutionState.h"
#include "Core/ExecutionTree.h"
#include "Core/Searcher.h"
#include "klee/ADT/RNG.h"

#include "llvm/Support/raw_ostream.h"

#include <memory>

using namespace klee;

namespace {

TEST(SearcherTest, PreferringSearcherMigratesConsumesAndIsFair) {
  auto child = std::make_unique<DFSSearcher>();
  PreferringSearcher preferring(std::move(child));
  ExecutionState ordinary;
  ExecutionState marked;
  ExecutionState forkChild;

  // DFS would keep selecting the last state (`marked`). Once that current
  // state is marked, the wrapper must move it out of DFS, not duplicate it in
  // both pools. Fair scheduling then gives the ordinary state a turn.
  preferring.update(nullptr, {&ordinary, &marked}, {});
  EXPECT_EQ(&preferring.selectState(), &marked);

  marked.interesting = true;
  preferring.update(&marked, {}, {});
  EXPECT_EQ(&preferring.selectState(), &marked);

  // No fork yet: the lease is still live, but preferred work cannot starve
  // the ordinary pool.
  preferring.update(&marked, {}, {});
  EXPECT_EQ(&preferring.selectState(), &ordinary);
  preferring.update(&ordinary, {}, {});
  EXPECT_EQ(&preferring.selectState(), &marked);

  // The next fork consumes the lease for the original and the new branch.
  preferring.update(&marked, {&forkChild}, {});
  EXPECT_FALSE(marked.interesting);
  EXPECT_FALSE(forkChild.interesting);
  EXPECT_EQ(&preferring.selectState(), &forkChild);

  preferring.update(&forkChild, {}, {&ordinary, &marked, &forkChild});
  EXPECT_TRUE(preferring.empty());
}

TEST(SearcherTest, RandomPath) {
  // First state
  ExecutionState es;
  InMemoryExecutionTree executionTree(es);

  RNG rng;
  RandomPathSearcher rp(&executionTree, rng);
  EXPECT_TRUE(rp.empty());

  rp.update(nullptr, {&es}, {});
  EXPECT_FALSE(rp.empty());
  EXPECT_EQ(&rp.selectState(), &es);

  // Two states
  ExecutionState es1(es);
  executionTree.attach(es.executionTreeNode, &es1, &es,
                       BranchType::Conditional);
  rp.update(&es, {&es1}, {});

  // Random path seed dependant
  EXPECT_EQ(&rp.selectState(), &es1);
  EXPECT_EQ(&rp.selectState(), &es);
  EXPECT_EQ(&rp.selectState(), &es1);

  rp.update(&es, {}, {&es1});
  for (int i = 0; i < 100; i++) {
    EXPECT_EQ(&rp.selectState(), &es);
  }

  rp.update(&es, {&es1}, {&es});
  executionTree.remove(es.executionTreeNode);
  for (int i = 0; i < 100; i++) {
    EXPECT_EQ(&rp.selectState(), &es1);
  }

  rp.update(&es1, {}, {&es1});
  executionTree.remove(es1.executionTreeNode);
  EXPECT_TRUE(rp.empty());
}

TEST(SearcherTest, TwoRandomPath) {
  // Root state
  ExecutionState root;
  InMemoryExecutionTree executionTree(root);

  ExecutionState es(root);
  executionTree.attach(root.executionTreeNode, &es, &root,
                       BranchType::Conditional);

  RNG rng, rng1;
  RandomPathSearcher rp(&executionTree, rng);
  RandomPathSearcher rp1(&executionTree, rng1);
  EXPECT_TRUE(rp.empty());
  EXPECT_TRUE(rp1.empty());

  rp.update(nullptr, {&es}, {});
  EXPECT_FALSE(rp.empty());
  EXPECT_TRUE(rp1.empty());
  EXPECT_EQ(&rp.selectState(), &es);

  // Two states
  ExecutionState es1(es);
  executionTree.attach(es.executionTreeNode, &es1, &es,
                       BranchType::Conditional);

  rp.update(&es, {}, {});
  rp1.update(nullptr, {&es1}, {});
  EXPECT_FALSE(rp1.empty());

  for (int i = 0; i < 100; i++) {
    EXPECT_EQ(&rp.selectState(), &es);
    EXPECT_EQ(&rp1.selectState(), &es1);
  }

  rp.update(&es, {&es1}, {&es});
  rp1.update(nullptr, {&es}, {&es1});

  for (int i = 0; i < 100; i++) {
    EXPECT_EQ(&rp1.selectState(), &es);
    EXPECT_EQ(&rp.selectState(), &es1);
  }

  rp1.update(&es, {}, {&es});
  executionTree.remove(es.executionTreeNode);
  EXPECT_TRUE(rp1.empty());
  EXPECT_EQ(&rp.selectState(), &es1);

  rp.update(&es1, {}, {&es1});
  executionTree.remove(es1.executionTreeNode);
  EXPECT_TRUE(rp.empty());
  EXPECT_TRUE(rp1.empty());

  executionTree.remove(root.executionTreeNode);
}

TEST(SearcherTest, TwoRandomPathDot) {
  std::stringstream modelExecutionTreeDot;
  ExecutionTreeNode *rootExecutionTreeNode, *rightLeafExecutionTreeNode,
      *esParentExecutionTreeNode, *es1LeafExecutionTreeNode,
      *esLeafExecutionTreeNode;

  // Root state
  ExecutionState root;
  InMemoryExecutionTree executionTree(root);
  rootExecutionTreeNode = root.executionTreeNode;

  ExecutionState es(root);
  executionTree.attach(root.executionTreeNode, &es, &root, BranchType::NONE);
  rightLeafExecutionTreeNode = root.executionTreeNode;
  esParentExecutionTreeNode = es.executionTreeNode;

  RNG rng;
  RandomPathSearcher rp(&executionTree, rng);
  RandomPathSearcher rp1(&executionTree, rng);

  rp.update(nullptr, {&es}, {});

  ExecutionState es1(es);
  executionTree.attach(es.executionTreeNode, &es1, &es, BranchType::NONE);
  esLeafExecutionTreeNode = es.executionTreeNode;
  es1LeafExecutionTreeNode = es1.executionTreeNode;

  rp.update(&es, {}, {});
  rp1.update(nullptr, {&es1}, {});

  // Compare ExecutionTree to model ExecutionTree
  modelExecutionTreeDot
      << "digraph G {\n"
      << "\tsize=\"10,7.5\";\n"
      << "\tratio=fill;\n"
      << "\trotate=90;\n"
      << "\tcenter = \"true\";\n"
      << "\tnode [style=\"filled\",width=.1,height=.1,fontname=\"Terminus\"]\n"
      << "\tedge [arrowsize=.3]\n"
      << "\tn" << rootExecutionTreeNode << " [shape=diamond];\n"
      << "\tn" << rootExecutionTreeNode << " -> n" << esParentExecutionTreeNode << " [label=0b011];\n"
      << "\tn" << rootExecutionTreeNode << " -> n" << rightLeafExecutionTreeNode << " [label=0b000];\n"
      << "\tn" << rightLeafExecutionTreeNode << " [shape=diamond,fillcolor=green];\n"
      << "\tn" << esParentExecutionTreeNode << " [shape=diamond];\n"
      << "\tn" << esParentExecutionTreeNode << " -> n" << es1LeafExecutionTreeNode << " [label=0b010];\n"
      << "\tn" << esParentExecutionTreeNode << " -> n" << esLeafExecutionTreeNode << " [label=0b001];\n"
      << "\tn" << esLeafExecutionTreeNode << " [shape=diamond,fillcolor=green];\n"
      << "\tn" << es1LeafExecutionTreeNode << " [shape=diamond,fillcolor=green];\n"
      << "}\n";
  std::string executionTreeDot;
  llvm::raw_string_ostream executionTreeDotStream(executionTreeDot);
  executionTree.dump(executionTreeDotStream);
  EXPECT_EQ(modelExecutionTreeDot.str(), executionTreeDotStream.str());

  rp.update(&es, {&es1}, {&es});
  rp1.update(nullptr, {&es}, {&es1});

  rp1.update(&es, {}, {&es});
  executionTree.remove(es.executionTreeNode);

  modelExecutionTreeDot.str("");
  modelExecutionTreeDot
      << "digraph G {\n"
      << "\tsize=\"10,7.5\";\n"
      << "\tratio=fill;\n"
      << "\trotate=90;\n"
      << "\tcenter = \"true\";\n"
      << "\tnode [style=\"filled\",width=.1,height=.1,fontname=\"Terminus\"]\n"
      << "\tedge [arrowsize=.3]\n"
      << "\tn" << rootExecutionTreeNode << " [shape=diamond];\n"
      << "\tn" << rootExecutionTreeNode << " -> n" << esParentExecutionTreeNode << " [label=0b001];\n"
      << "\tn" << rootExecutionTreeNode << " -> n" << rightLeafExecutionTreeNode << " [label=0b000];\n"
      << "\tn" << rightLeafExecutionTreeNode << " [shape=diamond,fillcolor=green];\n"
      << "\tn" << esParentExecutionTreeNode << " [shape=diamond];\n"
      << "\tn" << esParentExecutionTreeNode << " -> n" << es1LeafExecutionTreeNode << " [label=0b001];\n"
      << "\tn" << es1LeafExecutionTreeNode << " [shape=diamond,fillcolor=green];\n"
      << "}\n";

  executionTreeDot = "";
  executionTree.dump(executionTreeDotStream);
  EXPECT_EQ(modelExecutionTreeDot.str(), executionTreeDotStream.str());
  executionTree.remove(es1.executionTreeNode);
  executionTree.remove(root.executionTreeNode);
}

TEST(SearcherDeathTest, TooManyRandomPaths) {
  // First state
  ExecutionState es;
  InMemoryExecutionTree executionTree(es);
  executionTree.remove(es.executionTreeNode); // Need to remove to avoid leaks

  RNG rng;
  RandomPathSearcher rp(&executionTree, rng);
  RandomPathSearcher rp1(&executionTree, rng);
  RandomPathSearcher rp2(&executionTree, rng);
  ASSERT_DEATH({ RandomPathSearcher rp3(&executionTree, rng); }, "");
}
}
