#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <optional>
#include <vector>
#include "dimacs.h"

enum class LogicValue : uint8_t { Undef, True, False };

using SizeT = unsigned;

LogicValue operator!(LogicValue value) {
    switch (value) {
        case LogicValue::Undef: return LogicValue::Undef;
        case LogicValue::True:  return LogicValue::False;
        case LogicValue::False: return LogicValue::True;
    }
    return LogicValue::Undef;
}

using LogicSet = std::vector<LogicValue>;

struct Disjunct {
    explicit Disjunct(size_t numVariables):
        literals(numVariables, LogicValue::Undef) { }

    void setLiteral(size_t literal, bool value) {
        numUnsetLiterals += literals[literal] == LogicValue::Undef;
        literals[literal] = value ? LogicValue::True : LogicValue::False;
    }

    std::pair<size_t, LogicValue> findUnsetLiteralIndex(const LogicSet &interpret) const {
        for (size_t iVar = 0; iVar < literals.size(); iVar++)
            if (literals[iVar] != LogicValue::Undef && interpret[iVar] == LogicValue::Undef)
                return std::make_pair(iVar, literals[iVar]);

        return std::make_pair(std::numeric_limits<size_t>().max(), LogicValue::Undef);
    }

    LogicSet literals;
    size_t numUnsetLiterals = 0;
};

class CNF {
    struct SetVar {
        size_t variable;
        LogicValue value;

        bool operator<(const SetVar &other) {
            return variable < other.variable;
        }

        bool operator==(const SetVar &other) {
            return variable == other.variable;
        }
    };

    struct CnfState {
        std::vector<SizeT> disjunctsUnsetVariables;
        LogicSet interpret;
        LogicValue cachedValue = LogicValue::Undef;
        size_t numResolvedDisjuncts = 0;

        void create(const std::vector<Disjunct> &disjuncts, size_t numVariables) {
            interpret.assign(numVariables, LogicValue::Undef);
            disjunctsUnsetVariables.resize(disjuncts.size());
            for (size_t iDis = 0; iDis < disjuncts.size(); iDis++)
                disjunctsUnsetVariables[iDis] = disjuncts[iDis].numUnsetLiterals;
        }

        LogicValue setVariable(size_t variable, LogicValue value, const std::vector<Disjunct> &disjuncts) {
            assert(value != LogicValue::Undef);
            interpret[variable] = value;

            for (size_t iDis = 0; iDis < disjuncts.size(); iDis++)
                if (disjunctsUnsetVariables[iDis] &&
                    disjuncts[iDis].literals[variable] != LogicValue::Undef) {
                    if (disjuncts[iDis].literals[variable] == value) {
                        disjunctsUnsetVariables[iDis] = 0;
                        numResolvedDisjuncts++;
                    }
                    else if (--disjunctsUnsetVariables[iDis] == 0)
                        return cachedValue = LogicValue::False;
                }

            cachedValue = numResolvedDisjuncts == disjuncts.size() ? LogicValue::True : LogicValue::Undef;
            return cachedValue;
        }

        LogicValue setVariables(const std::vector<SetVar> &settedVariables, const std::vector<Disjunct> &disjuncts) {
            for (auto &setVar : settedVariables)
                interpret[setVar.variable] = setVar.value;

            for (size_t iDis = 0; iDis < disjuncts.size(); iDis++)
                if (disjunctsUnsetVariables[iDis]) {
                    for (auto &setVar : settedVariables)
                        if (disjuncts[iDis].literals[setVar.variable] != LogicValue::Undef) {
                            if (disjuncts[iDis].literals[setVar.variable] == setVar.value) {
                                // cachedDisjuncts[iDis] = LogicValue::True;
                                disjunctsUnsetVariables[iDis] = 0;
                                numResolvedDisjuncts++;
                                break;
                            }
                            else if (--disjunctsUnsetVariables[iDis] == 0)
                                return cachedValue = LogicValue::False;
                        }
                }

            cachedValue = numResolvedDisjuncts == disjuncts.size() ? LogicValue::True : LogicValue::Undef;
            return cachedValue;
        }
    };

    bool findUnitClauses(std::vector<SetVar> &settedVariables) {
        settedVariables.clear();

        for (size_t iDis = 0; iDis < disjuncts.size(); iDis++)
            if (currentState.disjunctsUnsetVariables[iDis] == 1) {
                auto [variable, value] = disjuncts[iDis].findUnsetLiteralIndex(currentState.interpret);
                settedVariables.push_back({variable, value});
            }

        std::sort(settedVariables.begin(), settedVariables.end());
        auto end = std::unique(settedVariables.begin(), settedVariables.end());
        settedVariables.erase(end, settedVariables.end());
        return !settedVariables.empty();
    }

    const Disjunct *findUndefClause() {
        for (size_t iDis = 0; iDis < disjuncts.size(); iDis++)
            if (currentState.disjunctsUnsetVariables[iDis])
                return &disjuncts[iDis];
        return nullptr;
    }

public:
    CNF(size_t numVariables, size_t numClauses):
        numVariables(numVariables) {
            disjuncts.reserve(numClauses);
        }

    // dpll algorithm
    bool checkSatisfiability() {
        if (disjuncts.empty())
            return true;

        currentState.create(disjuncts, numVariables);
        std::vector<SetVar> settedVariables;

        do {
            if (currentState.cachedValue == LogicValue::True)
                return true;

            while (currentState.cachedValue == LogicValue::Undef && findUnitClauses(settedVariables))
                currentState.setVariables(settedVariables, disjuncts);

            if (currentState.cachedValue == LogicValue::Undef) {
                const auto *disjunct = findUndefClause();
                if (!disjunct)
                    assert(0 && "unreachable");

                auto [variable, value] = disjunct->findUnsetLiteralIndex(currentState.interpret);
                stateStack.push_back(currentState);
                currentState.setVariable(variable, value, disjuncts);
                stateStack.back().setVariable(variable, !value, disjuncts);
            }

            while (currentState.cachedValue == LogicValue::False && !stateStack.empty()) {
                currentState = std::move(stateStack.back());
                stateStack.pop_back();
            }
        } while (currentState.cachedValue == LogicValue::Undef);

        return currentState.cachedValue == LogicValue::True;
    }

    void addDisjunct(int *literalBuffer, int numLiterals) {
        if (!numLiterals)
            return;

        if (!literalBuffer || numLiterals < 0) {
            std::cerr << "There is bug in parser\n";
            return;
        }

        auto &disjunct = disjuncts.emplace_back(numVariables);
        for (int iLiteral = 0; iLiteral < numLiterals; iLiteral++) {
            auto literal = literalBuffer[iLiteral];
            if (literal == 0) {
                std::cerr << "There is bug in parser\n";
                return;
            }

            if (std::abs(literal) > numVariables) {
                std::cerr << "Incorrect file: value" << literalBuffer[iLiteral] << "is out of CNF variables\n";
                return;
            }

            disjunct.setLiteral(std::abs(literal) - 1, literal > 0);
        }
    }

private:
    std::vector<Disjunct> disjuncts;
    CnfState currentState;
    std::vector<CnfState> stateStack;
    const size_t numVariables;
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
