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

#include <string>
#include <set>

#include "souper/Inst/Inst.h"

#include "llvm/Support/raw_ostream.h"

class InstGraph {
  llvm::raw_ostream &O;
  souper::Inst* Root;
  static unsigned graphNum;
  std::string Name = "Graph";
  // graph is laid bottom to top
  std::string Rankdir = "BT";
  std::set<souper::Inst*> Visited;

  void writeHeader();
  void writeFooter() { O << "}\n"; }

  void writeNodeProperties(souper::Inst* I);
  std::string getNodeName(souper::Inst* I);
  void writeRecursive(souper::Inst* I);

public:
  InstGraph(llvm::raw_ostream &O, souper::Inst* Root) : O(O), Root(Root) {
    Name.append(std::to_string(graphNum++));
  }

  // write the graph to the member variable raw_ostream
  void write();
};
