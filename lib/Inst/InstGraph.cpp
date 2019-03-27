// Copyright 2019 The Souper Authors. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <vector>

#include "llvm/ADT/StringRef.h"

#include "souper/Inst/Inst.h"
#include "souper/Inst/InstGraph.h"

unsigned InstGraph::graphNum = 0;

using namespace souper;

void InstGraph::writeNodeProperties(Inst* I) {
  // properties already written; don't write again.
  if (Visited.find(I) != Visited.end())
    return;

  Visited.insert(I);

  if (I == Root) {
    O << getNodeName(I) << " [style=bold];\n";
    return;
  }

  switch(I->K) {
  case Inst::Kind::ReservedConst:
  case Inst::Kind::ReservedInst:
  case Inst::Kind::Var:
    O << getNodeName(I) << " [shape=box];\n";
    break;
  }
}

std::string InstGraph::getNodeName(Inst* I) {
  switch(I->K) {
  case Inst::Kind::Const:
    return "\"Const " + I->Val.toString(10, true) + "\"";
  case Inst::Kind::Var:
    return "\"Var " + I->Name + "\"";
  case Inst::Kind::ReservedConst:
  case Inst::Kind::ReservedInst:
    return "\"Reserved " + I->Name + "\"";
  default:
    return "\"" + std::string(Inst::getKindName(I->K)) + "\"";
  }
}

void InstGraph::writeRecursive(Inst* I) {
  if (I->Ops.size() == 0) {
    return;
  }

  for (auto &Ops : I->Ops) {
    writeRecursive(Ops);

    writeNodeProperties(I);
    writeNodeProperties(Ops);

    O << getNodeName(I);
    O << " -> ";
    O << getNodeName(Ops);
    O << ";\n";
  }
}

void InstGraph::writeHeader() {
  O << "digraph " << Name << " { " << '\n';

  // graph properties
  O << "rankdir = " << Rankdir << ";\n";
}

void InstGraph::write() {
  writeHeader();

  Visited.clear();
  writeRecursive(Root);

  writeFooter();
}
