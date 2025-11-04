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

struct SettedVariable {
    SizeT variable;
    LogicValue value;

    bool operator<(const SettedVariable &other) {
        return variable < other.variable;
    }

    bool operator==(const SettedVariable &other) {
        return variable == other.variable;
    }
};

struct Disjunct {
    explicit Disjunct(size_t numVariables):
        literals(numVariables, LogicValue::Undef) { }

    void setLiteral(size_t literal, bool value) {
        numUnsetLiterals += literals[literal] == LogicValue::Undef;
        literals[literal] = value ? LogicValue::True : LogicValue::False;
    }

    SettedVariable findUnsetLiteralIndex(const LogicSet &interpret) const {
        for (size_t iVar = 0; iVar < literals.size(); iVar++)
            if (literals[iVar] != LogicValue::Undef && interpret[iVar] == LogicValue::Undef)
                return {SizeT(iVar), literals[iVar]};

        return {std::numeric_limits<SizeT>().max(), LogicValue::Undef};
    }

    LogicSet literals;
    size_t numUnsetLiterals = 0;
};

class CnfState {
    LogicValue setVariables(const std::vector<Disjunct> &disjuncts, const std::vector<SettedVariable> &settedVariables) {
        for (auto &setVar : settedVariables)
            interpret[setVar.variable] = setVar.value;

        SizeT prevListNode = disjunctList.size() - 1;
        for (SizeT iDis = disjunctList.back(); iDis != disjunctsListEnd; iDis = disjunctList[iDis]) {
            for (auto &setVar : settedVariables)
                if (disjuncts[iDis].literals[setVar.variable] != LogicValue::Undef) {
                    if (disjuncts[iDis].literals[setVar.variable] == setVar.value) {
                        disjunctsUnsetVariables[iDis] = 0;
                        break;
                    }
                    else if (--disjunctsUnsetVariables[iDis] == 0)
                        return cachedValue = LogicValue::False;
                }

            if (disjunctsUnsetVariables[iDis]) {
                disjunctList[prevListNode] = iDis;
                prevListNode = iDis;
            }
        }

        disjunctList[prevListNode] = disjunctsListEnd;
        cachedValue = prevListNode == disjunctList.size() - 1 ? LogicValue::True : LogicValue::Undef;
        return cachedValue;
    }

    bool findUnitClauses(const std::vector<Disjunct> &disjuncts, std::vector<SettedVariable> &settedVariables) {
        settedVariables.clear();

        for (size_t iDis = disjunctList.back(); iDis != disjunctsListEnd; iDis = disjunctList[iDis])
            if (disjunctsUnsetVariables[iDis] == 1) {
                auto variable = disjuncts[iDis].findUnsetLiteralIndex(interpret);
                settedVariables.push_back(variable);
            }

        std::sort(settedVariables.begin(), settedVariables.end());
        auto end = std::unique(settedVariables.begin(), settedVariables.end());
        settedVariables.erase(end, settedVariables.end());
        return !settedVariables.empty();
    }

    const Disjunct *findUndefClause(const std::vector<Disjunct> &disjuncts) {
        for (size_t iDis = disjunctList.back(); iDis != disjunctsListEnd; iDis = disjunctList[iDis])
            if (disjunctsUnsetVariables[iDis])
                return &disjuncts[iDis];
        return nullptr;
    }

public:
    void create(const std::vector<Disjunct> &disjuncts, size_t numVariables) {
        const auto numDisjuncts = disjuncts.size();
        interpret.assign(numVariables, LogicValue::Undef);
        disjunctsUnsetVariables.resize(numDisjuncts);
        disjunctList.resize(numDisjuncts + 1);

        for (size_t iDis = 0; iDis < numDisjuncts; iDis++) {
            disjunctsUnsetVariables[iDis] = disjuncts[iDis].numUnsetLiterals;
            disjunctList[iDis] = iDis + 1;
        }

        // last slot points to list start
        disjunctList[numDisjuncts - 1] = disjunctsListEnd;
        disjunctList[numDisjuncts] = 0;
    }

    LogicValue getCachedValue() const {
        return cachedValue;
    }

    void makeUnitPropagation(const std::vector<Disjunct> &disjuncts, std::vector<SettedVariable> &settedVariables) {
        while (cachedValue == LogicValue::Undef && findUnitClauses(disjuncts, settedVariables))
            setVariables(disjuncts, settedVariables);
    }

    void makeEnumeration(const std::vector<Disjunct> &disjuncts, std::vector<SettedVariable> &settedVariables, CnfState &copy) {
        const auto *disjunct = findUndefClause(disjuncts);
        assert(disjunct);

        settedVariables.resize(1);
        settedVariables[0] = disjunct->findUnsetLiteralIndex(interpret);
        setVariables(disjuncts, settedVariables);
        settedVariables[0].value = !settedVariables[0].value;
        copy.setVariables(disjuncts, settedVariables);
    }

private:
    std::vector<SizeT> disjunctsUnsetVariables, disjunctList;
    LogicSet interpret;
    LogicValue cachedValue = LogicValue::Undef;
    static constexpr SizeT disjunctsListEnd = std::numeric_limits<SizeT>().max();
};

class CNF {
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
        std::vector<SettedVariable> settedVariables;

        do {
            if (currentState.getCachedValue() == LogicValue::True)
                return true;

            // Unit propagation
            currentState.makeUnitPropagation(disjuncts, settedVariables);

            // Enumeration
            if (currentState.getCachedValue() == LogicValue::Undef) {
                stateStack.push_back(currentState);
                currentState.makeEnumeration(disjuncts, settedVariables, stateStack.back());
            }

            // Rollback
            while (currentState.getCachedValue() == LogicValue::False && !stateStack.empty()) {
                currentState = std::move(stateStack.back());
                stateStack.pop_back();
            }
        } while (currentState.getCachedValue() == LogicValue::Undef);

        return currentState.getCachedValue() == LogicValue::True;
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
void addDisjunct(void *cnfPtr, int /* numClauses */, int *literalBuffer, int numLiterals) {
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
