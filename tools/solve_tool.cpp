// A batch solver over the extracted proofs, used only to generate the word
// tables the solving chain needs. Nothing it prints is trusted: every word it
// produces is rechecked inside Rocq by computing what the word denotes.
//
// Input, one cube per line: a mode letter, then eight corner slots as
// "piece twist" and twelve edge slots as "piece flip", all as numbers.
// Mode "F" solves with all eighteen moves, "D" with only the ten the second
// phase may use. Output is the move codes of a solution, or "FAIL".

#include "rubik.h"

#include <iostream>
#include <sstream>
#include <string>
#include <vector>

namespace {

std::vector<std::uint64_t> codes(const List::list<move> &p) {
  std::vector<std::uint64_t> out;
  const List::list<move> *cur = &p;
  List::list<move> hold;
  while (std::holds_alternative<List::list<move>::Cons>(cur->v())) {
    const auto &cons = std::get<List::list<move>::Cons>(cur->v());
    out.push_back(Viewer::move_code(cons.a));
    if (!cons.l) break;
    hold = *cons.l;
    cur = &hold;
  }
  return out;
}

} // namespace

int main() {
  const auto t1 = Phase1::build_tables1(std::monostate{});
  const auto t2 = Phase2::build_tables2(std::monostate{});
  std::string line;
  while (std::getline(std::cin, line)) {
    if (line.empty()) continue;
    std::istringstream in(line);
    std::string mode;
    in >> mode;
    cube c{};
    cslot *cs[8] = {&c.xURF, &c.xUFL, &c.xULB, &c.xUBR,
                    &c.xDFR, &c.xDLF, &c.xDBL, &c.xDRB};
    eslot *es[12] = {&c.yUR, &c.yUF, &c.yUL, &c.yUB, &c.yDR, &c.yDF,
                     &c.yDL, &c.yDB, &c.yFR, &c.yFL, &c.yBL, &c.yBR};
    for (auto *slot : cs) {
      int p = 0, t = 0;
      in >> p >> t;
      *slot = cslot{static_cast<Corner>(p), static_cast<Twist>(t)};
    }
    for (auto *slot : es) {
      int p = 0, f = 0;
      in >> p >> f;
      *slot = eslot{static_cast<Edge>(p), static_cast<Flip>(f)};
    }
    const auto answer = mode == "D" ? Phase2::phase2(t2, 30, c)
                                    : Solve::two_phase(t1, t2, 20, 30, c);
    if (!answer) {
      std::cout << "FAIL\n";
    } else {
      const auto out = codes(*answer);
      for (std::size_t i = 0; i < out.size(); ++i)
        std::cout << (i ? " " : "") << out[i];
      std::cout << "\n";
    }
    std::cout.flush();
  }
  return 0;
}
