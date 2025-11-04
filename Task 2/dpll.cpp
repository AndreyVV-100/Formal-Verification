#include <algorithm>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <optional>
#include <vector>
#include "dimacs.h"

enum class LogicValue : uint8_t { Undef, True, False };

LogicValue operator!(LogicValue value) {
    switch (value) {
        case LogicValue::Undef: return LogicValue::Undef;
        case LogicValue::True:  return LogicValue::False;
        case LogicValue::False: return LogicValue::True;
    }
    return LogicValue::Undef;
}

struct PartialInterpretation {
    static constexpr size_t N = 256;

    explicit PartialInterpretation(size_t numVariables) {
        assert(numVariables <= N);
        undefMask.set();
    }

    size_t size() const {
        return trueMask.size();
    }

    LogicValue operator[](size_t index) const {
        return undefMask[index] ? LogicValue::Undef :
                                  trueMask[index] ? LogicValue::True : LogicValue::False;
    }

    void set(size_t index, LogicValue value) {
        trueMask[index] = value == LogicValue::True;
        undefMask[index] = value == LogicValue::Undef;
    }

    // I'm so tired and haven't energy to use __m256i here
    std::bitset<N> trueMask, undefMask;
};

class Disjunct {
public:
    explicit Disjunct(size_t numVariables):
        literals(numVariables) {}

    void setLiteral(size_t literal, bool value) {
        literals.trueMask[literal] = value;
        literals.undefMask[literal] = false;
    }

    LogicValue compute(const PartialInterpretation &interpret) {
        if (cachedValue != LogicValue::Undef)
            return cachedValue;

        return recompute(interpret);
    }

    LogicValue recompute(const PartialInterpretation &interpret) {
        bool countTrue  = (~literals.undefMask & ~interpret.undefMask & ~(literals.trueMask ^ interpret.trueMask)).any();
        if (countTrue)
            return cachedValue = LogicValue::True;

        return cachedValue = getNumUnsetLiterals(interpret) > 0 ? LogicValue::Undef : LogicValue::False;
    }

    LogicValue rollbackRecompute(const PartialInterpretation &interpret, size_t variable) {
        if (literals[variable] == LogicValue::Undef)
            return cachedValue;
        return recompute(interpret);
    }

    size_t getNumUnsetLiterals(const PartialInterpretation &interpret) const {
        return (~literals.undefMask & interpret.undefMask).count();
    }

    std::pair<size_t, LogicValue> findUnsetLiteralIndex(const PartialInterpretation &interpret) const {
        auto index = (~literals.undefMask & interpret.undefMask)._Find_first();
        return std::make_pair(index, literals[index]);
    }

private:
    PartialInterpretation literals;
    LogicValue cachedValue = LogicValue::Undef;
};

class CNF {
    enum class ActionType {
        OnePropagation,
        EnumerationDirect,
        EnumerationInverted
    };

    struct Action {
        size_t variable;
        ActionType type;
    };

    const Disjunct *findUnitClause() {
        auto it = std::find_if(disjuncts.begin(), disjuncts.end(),
                        [this](Disjunct &disjunst) {
                            return disjunst.recompute(interpret)  == LogicValue::Undef &&// disjunst.getCachedValue() == LogicValue::Undef &&
                                   disjunst.getNumUnsetLiterals(interpret) == 1;
                        });
        return it != disjuncts.end() ? &*it : nullptr;
    }

    const Disjunct *findUndefClause() {
        auto it = std::find_if(disjuncts.begin(), disjuncts.end(),
                        [this](Disjunct &disjunst) {
                            return disjunst.recompute(interpret)  == LogicValue::Undef &&// disjunst.getCachedValue() == LogicValue::Undef &&
                                   disjunst.getNumUnsetLiterals(interpret);
                        });
        return it != disjuncts.end() ? &*it : nullptr;
    }

    LogicValue compute() {
        if (cachedValue != LogicValue::Undef)
            return cachedValue;

        bool hasUndef = false;
        for (auto &disjunct : disjuncts) {
            auto value = disjunct.compute(interpret);
            if (value == LogicValue::False)
                return cachedValue = LogicValue::False;
            if (value == LogicValue::Undef)
                hasUndef = true;
        }

        return cachedValue = hasUndef ? LogicValue::Undef : LogicValue::True;
    }

    LogicValue rollbackRecompute(size_t variable) {
        cachedValue = LogicValue::True;
        for (auto &disjunct : disjuncts) {
            auto value = disjunct.rollbackRecompute(interpret, variable);
            if (value == LogicValue::False)
                cachedValue = LogicValue::False;
            if (value == LogicValue::Undef && cachedValue != LogicValue::False)
                cachedValue = LogicValue::Undef;
        }

        return cachedValue;
    }

    LogicValue recompute() {
        bool hasUndef = false;
        for (auto &disjunct : disjuncts) {
            auto value = disjunct.recompute(interpret);
            if (value == LogicValue::False)
                return cachedValue = LogicValue::False;
            if (value == LogicValue::Undef)
                hasUndef = true;
        }

        return cachedValue = hasUndef ? LogicValue::Undef : LogicValue::True;
    }

public:
    CNF(size_t numVariables, size_t numClauses):
        interpret(numVariables) {
            disjuncts.reserve(numClauses);
        }

    // dpll algorithm
    bool checkSatisfiability() {
        if (disjuncts.empty())
            return true;

        do {
            if (cachedValue == LogicValue::True)
                return true;

            const Disjunct *disjunct; 
            while ((disjunct = findUnitClause())) {
                auto [variable, value] = disjunct->findUnsetLiteralIndex(interpret);
                interpret.set(variable, value);
                actions.push_back({variable, ActionType::OnePropagation});
            }

            compute();
            if (cachedValue == LogicValue::Undef) {
                disjunct = findUndefClause();
                if (!disjunct)
                    assert(0 && "unreachable");

                auto [variable, value] = disjunct->findUnsetLiteralIndex(interpret);
                interpret.set(variable, value);
                actions.push_back({variable, ActionType::EnumerationDirect});

                if (compute() == LogicValue::False) {
                    interpret.set(variable, !value);
                    rollbackRecompute(variable);
                    actions.back().type = ActionType::EnumerationInverted;
                }
            }

            // rollback
            if (cachedValue == LogicValue::False) {
                while (!actions.empty()) {
                    auto &action = actions.back();
                    if (action.type == ActionType::EnumerationDirect) {
                        interpret.set(action.variable, !interpret[action.variable]);
                        if (recompute() != LogicValue::False) {
                            action.type = ActionType::EnumerationInverted;
                            break; // successful rollback
                        }
                    }
                    interpret.set(action.variable, LogicValue::Undef);
                    actions.pop_back();
                }
            }
        } while (!actions.empty());

        return false;
    }

    void addDisjunct(int *literalBuffer, int numLiterals) {
        if (!numLiterals)
            return;

        if (!literalBuffer || numLiterals < 0) {
            std::cerr << "There is bug in parser\n";
            return;
        }

        auto &disjunct = disjuncts.emplace_back(interpret.size());
        for (int iLiteral = 0; iLiteral < numLiterals; iLiteral++) {
            auto literal = literalBuffer[iLiteral];
            if (literal == 0) {
                std::cerr << "There is bug in parser\n";
                return;
            }

            if (std::abs(literal) > interpret.size()) {
                std::cerr << "Incorrect file: value" << literalBuffer[iLiteral] << "is out of CNF variables\n";
                return;
            }

            disjunct.setLiteral(std::abs(literal) - 1, literal > 0);
        }
    }

private:
    std::vector<Disjunct> disjuncts;
    PartialInterpretation interpret;
    std::vector<Action> actions;
    LogicValue cachedValue = LogicValue::Undef;
};

// dimacs_header_func
void createCnf(void *cnfPtr, int numVariables, int numClauses) {
    assert(cnfPtr);
    static_cast<std::optional<CNF>*>(cnfPtr)->emplace(numVariables, numClauses);
}

// dimacs_clause_func
void addDisjunct(void *cnfPtr, int numClauses, int *literalBuffer, int numLiterals) {
    assert(cnfPtr);
    auto *cnf = static_cast<std::optional<CNF>*>(cnfPtr);
    if (!cnf->has_value()) {
        std::cerr << "Incorrect file: no CNF header\n";
        return;
    }

    (*cnf)->addDisjunct(literalBuffer, numLiterals);
}

int main(int argc, char **argv) {
    if (argc < 2) {
        std::cerr << "No input file!\n";
        return 1;
    }

    FILE *file = fopen(argv[1], "r");
    if (!file) {
        std::cerr << "Can't open input file!\n";
        return 1;
    }

    std::optional<CNF> cnf;
    dimacs_fread(file, &cnf, createCnf, addDisjunct);

    if (cnf->checkSatisfiability())
        std::cout << "SAT\n";
    else
        std::cout << "UNSAT\n";

    return 0;
}
