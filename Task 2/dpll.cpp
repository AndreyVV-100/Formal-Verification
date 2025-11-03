#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
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

using PartialInterpretation = std::vector<LogicValue>;

class Disjunct {
public:
    explicit Disjunct(size_t numVariables):
        literals(numVariables, LogicValue::Undef) {}

    void setLiteral(size_t literal, LogicValue value) {
        if (literals[literal] == LogicValue::Undef && value != LogicValue::Undef) {
            numImportantLiterals++;
            numUnsetLiterals++;
        }
        literals[literal] = value;
    }

    LogicValue getCachedValue() const {
        return cachedValue;
    }

    LogicValue compute(const PartialInterpretation &interpret) {
        if (cachedValue != LogicValue::Undef)
            return cachedValue;

        return recompute(interpret);
    }

    LogicValue recompute(const PartialInterpretation &interpret) {
        assert(interpret.size() == literals.size());

        numUnsetLiterals = numImportantLiterals;
        for (size_t iVar = 0; iVar < literals.size(); iVar++)
            if (literals[iVar] != LogicValue::Undef) {
                if (interpret[iVar] != LogicValue::Undef)
                    numUnsetLiterals--;
                if (literals[iVar] == interpret[iVar])
                    return cachedValue = LogicValue::True;
            }

        return cachedValue = numUnsetLiterals > 0 ? LogicValue::Undef : LogicValue::False;
    }

    LogicValue rollbackRecompute(const PartialInterpretation &interpret, size_t variable) {
        assert(interpret.size() == literals.size());
        if (literals[variable] == LogicValue::Undef)
            return cachedValue;
        return recompute(interpret);
    }

    size_t getNumUnsetLiterals() const {
        return numUnsetLiterals;
    }

    std::pair<size_t, LogicValue> findUnsetLiteralIndex(const PartialInterpretation &interpret) const {
        assert(interpret.size() == literals.size());

        for (size_t iVar = 0; iVar < literals.size(); iVar++)
            if (literals[iVar] != LogicValue::Undef && interpret[iVar] == LogicValue::Undef)
                return std::make_pair(iVar, literals[iVar]);

        return std::make_pair(std::numeric_limits<size_t>().max(), LogicValue::Undef);
    }

private:
    // IsTrue  <==> (.. ||  a_i || ..)
    // IsFalse <==> (.. || !a_i || ..)
    PartialInterpretation literals;
    size_t numImportantLiterals = 0, numUnsetLiterals = 0;
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
                        [](const Disjunct &disjunst) {
                            return disjunst.getCachedValue() == LogicValue::Undef &&
                                   disjunst.getNumUnsetLiterals() == 1;
                        });
        return it != disjuncts.end() ? &*it : nullptr;
    }

    const Disjunct *findUndefClause() {
        auto it = std::find_if(disjuncts.begin(), disjuncts.end(),
                        [](const Disjunct &disjunst) {
                            return disjunst.getCachedValue() == LogicValue::Undef &&
                                   disjunst.getNumUnsetLiterals();
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
        bool hasUndef = false;
        for (auto &disjunct : disjuncts) {
            auto value = disjunct.rollbackRecompute(interpret, variable);
            if (value == LogicValue::False)
                return cachedValue = LogicValue::False;
            if (value == LogicValue::Undef)
                hasUndef = true;
        }

        return cachedValue = hasUndef ? LogicValue::Undef : LogicValue::True;
    }

#if 0
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
#endif

public:
    CNF(size_t numVariables, size_t numClauses):
        interpret(numVariables, LogicValue::Undef) {
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
            while ((disjunct = findUnitClause()) && cachedValue == LogicValue::Undef) {
                auto [variable, value] = disjunct->findUnsetLiteralIndex(interpret);
                interpret[variable] = value;
                compute();
                actions.push_back({variable, ActionType::OnePropagation});
            }

            if (cachedValue == LogicValue::Undef) {
                disjunct = findUndefClause();
                if (!disjunct)
                    assert(0 && "unreachable");

                auto [variable, value] = disjunct->findUnsetLiteralIndex(interpret);
                interpret[variable] = value;
                actions.push_back({variable, ActionType::EnumerationDirect});

                if (compute() == LogicValue::False) {
                    interpret[variable] = !value;
                    rollbackRecompute(variable);
                    actions.back().type = ActionType::EnumerationInverted;
                }
            }

            // rollback
            if (cachedValue == LogicValue::False) {
                while (!actions.empty()) {
                    auto &action = actions.back();
                    if (action.type == ActionType::EnumerationDirect) {
                        interpret[action.variable] = !interpret[action.variable];
                        if (rollbackRecompute(action.variable) != LogicValue::False) {
                            action.type = ActionType::EnumerationInverted;
                            break; // successful rollback
                        }
                    }
                    interpret[action.variable] = LogicValue::Undef;
                    rollbackRecompute(action.variable);
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

            disjunct.setLiteral(std::abs(literal) - 1, literal > 0 ? LogicValue::True : LogicValue::False);
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
