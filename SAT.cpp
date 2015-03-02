#include <iostream>
//#include <fstream>
//#include <sstream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

class Literal
{
public:
    Literal() {
        value = UNDEF;      // model, actually
        occurrences = 0;
    }

    int value;
    int occurrences;
    vector<int> /*inClauses,*/ negatives, positives;   // clausules on apareix el literal i-essim 
};


uint numVars;
uint numClauses;
vector<vector<int> > clauses;
vector<Literal> lits;
//vector<uint> varPerClauseUndef;

vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;
uint varsAssigned;
//uint indexOfNextLitToDecide;

vector< pair<int, int> > heuristByAppear;           // [numVars]

struct Comp {
   bool operator() (const pair<int, int> &a, const pair<int, int> &b)
   {
       return a.first > b.first;
   }
};


void readClauses( ){
    // Skip comments
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
    }  
    // Read "cnf numVars numClauses"
    string aux;
    cin >> aux >> numVars >> numClauses;
    cout << "numVars: " << numVars << endl;
    cout << "numClauses: " << numClauses << endl;
    
    lits.resize(numVars+1);
    clauses.resize(numClauses);
    //varPerClauseUndef.resize(numClauses);

    // Read clauses
    for (uint i = 0; i < numClauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) {
            clauses[i].push_back(lit);
            
            ++lits[abs(lit)].occurrences;
            //++varPerClauseUndef[abs(lit)];

            if (lit > 0) lits[lit].positives.push_back(i);
            else lits[abs(lit)].negatives.push_back(i);
            //lits[abs(lit)].inClauses.push_back(i);
        }
    }

    /*cout << "--- LITERALS ---" << endl;
    for (int i = 1; i < numVars+1; ++i) {
        cout << "\tlit " << i << ", occurrences: " << lits[i].occurrences << endl;
        cout << "\t\tpos: " << lits[i].positives.size() << ", neg: " << lits[i].negatives.size() << endl;
        cout << "\t\t(+):";
        for (int j = 0; j < lits[i].positives.size(); ++j) cout << " " << lits[i].positives[j];
        cout << endl << "\t\t(-):";
        for (int j = 0; j < lits[i].negatives.size(); ++j) cout << " " << lits[i].negatives[j];
        cout << endl << "\t\t(U):";
        for (int j = 0; j < lits[i].inClauses.size(); ++j) cout << " " << lits[i].inClauses[j];
        cout << endl;
    }*/

    // Sort variables by occurrences
    heuristByAppear.resize(numVars);
    for (uint i = 1; i < numVars+1; ++i) {
        heuristByAppear[i-1] = make_pair(lits[i].occurrences, i);    
        //int diff = lits[i].positives.size() - lits[i].negatives.size();
        //heuristByAppear[i-1] = make_pair( abs(diff), i);
    }
    sort(heuristByAppear.begin(), heuristByAppear.end(), Comp());
    /*cout << "--- SORTED ---" << endl;
    for (int i = 0; i < heuristByAppear.size(); ++i) {
        cout << "#" << heuristByAppear[i].first << " <- " << heuristByAppear[i].second << endl;
    }
    cout << "--------------" << endl;*/
}


int currentValueInModel(int lit) {
    if (lit > 0) return lits[lit].value;
    else {
        if (lits[-lit].value == UNDEF) return UNDEF;
        return 1 - lits[-lit].value;
    }
}


void setLiteralToTrue(int lit) {
    modelStack.push_back(lit);
    ++varsAssigned;
    if (lit > 0) {
        lits[lit].value = TRUE;
        
        /*for (int i = 0; i < lits[lit].inClauses.size(); ++i) {
            --varPerClauseUndef[ lits[lit].inClauses[i] ];
        }*/
    }
    else {
        lits[-lit].value = FALSE;
        
        /*for (int i = 0; i < lits[-lit].inClauses.size(); ++i) {
            --varPerClauseUndef[ lits[-lit].inClauses[i] ];
        }*/
    }
}


bool checkConflicts() {
    while ( indexOfNextLitToPropagate < modelStack.size() ) {
        int var = abs(modelStack[indexOfNextLitToPropagate]);
        vector<int> *clausesToCheck; // = lits[var].inClauses;
        if (lits[var].value == TRUE)        clausesToCheck = &lits[var].negatives;
        else if (lits[var].value == FALSE)  clausesToCheck = &lits[var].positives;

        
        /*cout << "--------------------" << endl;
        cout << "modelStack:";  for (int i = 0; i < modelStack.size(); ++i) cout << " " << modelStack[i] << "(" << i << ")";
        cout << endl;
        int k = 0; 
        for (int i = 0; i < modelStack.size(); ++i) {
            if (modelStack[i] != 0) ++k;
        }
        cout << "varsAssigned: " << varsAssigned << ", counted(" << k << ")" << endl;   
        cout << "indexOfNextLitToDecide: " << indexOfNextLitToDecide << endl;
        cout << "indexOfNextLitToPropagate: " << indexOfNextLitToPropagate << endl;
        cout << "modelStack[indexOf]: " << modelStack[indexOfNextLitToPropagate] << endl;
        cout << "var: " << var << endl;
        //cout << "lits[ abs(modelStack[indexOf]) ].value: " << lits[var].value << endl;
            //cout << "clausesToCheck:"; for(int k = 0; k < clausesToCheck.size(); ++k) cout << " " << clausesToCheck[k];
            //cout << endl;

        cout << "--------------------" << endl;*/

        ++indexOfNextLitToPropagate;

        for (int i = 0; i < clausesToCheck->size(); ++i) {
            int clause = (*clausesToCheck)[i];

            //if (varPerClauseUndef[ clause ] > 0) {
                bool someLitTrue = false;
                int numUndefs = 0;
                int lastLitUndef = 0;
                for (uint k = 0; not someLitTrue and k < clauses[ clause ].size(); ++k) {
                    int val = currentValueInModel(clauses[ clause ][k]);
                    if (val == TRUE) someLitTrue = true;
                    else if (val == UNDEF) { ++numUndefs; lastLitUndef = clauses[ clause ][k]; }
                }
                if (not someLitTrue and numUndefs == 0) return true; // conflict! all lits false
                else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);        // modelStack.push_back()    
            }
        //}
    }
    return false;
}


void backtrack() {
    //cout << endl << " -BACKTRACK- " << endl;
    uint i = modelStack.size() - 1;
    int lit = 0;
    while (modelStack[i] != 0) { // 0 is the DL mark
        lit = modelStack[i];
        lits[abs(lit)].value = UNDEF;
        //model[abs(lit)] = UNDEF;
        /*for (int j = 0; j < lits[abs(lit)].inClauses.size(); ++j)
            ++varPerClauseUndef[ lits[abs(lit)].inClauses[j] ];*/
        modelStack.pop_back();
        --varsAssigned;
        --i;
    }
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    /*--indexOfNextLitToDecide;
    i = indexOfNextLitToDecide;
    cout << "start decision backtracking at var " << heuristByAppear[i].second << " (" << i << ")" << endl;
    while ( lits[ heuristByAppear[i].second ].value != UNDEF) {
        --indexOfNextLitToDecide;
        --i;
    }*/
    indexOfNextLitToPropagate = modelStack.size();
    setLiteralToTrue(-lit);  // reverse last decision
}


// Heuristic for finding the next decision literal:
int getNextDecisionLiteral() {
    for (uint i = 0; i < numVars; ++i) {
        if (lits[ heuristByAppear[i].second ].value == UNDEF) {
                //indexOfNextLitToDecide = i;
                //cout << "\tDecide i: " << indexOfNextLitToDecide << endl;
                //cout << "\ti returned -> " << i << " (varsAssigned:" << varsAssigned << ")" << endl;
            return heuristByAppear[i].second;
            //cout << "[i:" << i << "] heuristByAppear[i].second: " << heuristByAppear[i].second << ", (+) " << lits[ heuristByAppear[i].second+1 ].positives.size() << ", (-) " << lits[ heuristByAppear[i].second+1 ].positives.size() << endl;
            /*if (lits[ heuristByAppear[i].second+1 ].positives.size() >= lits[ heuristByAppear[i].second+1 ].negatives.size())
                return heuristByAppear[i].second;
            else 
                return -heuristByAppear[i].second;*/
        }
        //else cout << "\t<" << heuristByAppear[i].first << ", " << heuristByAppear[i].second << "> already assigned" << endl;
    }
    //if (varsAssigned < numVars)
    //    return heuristByAppear[ varsAssigned ].second;
    return 0;                               // reurns 0 when all literals are defined
}

void checkmodel() {
    for (int i = 0; i < numClauses; ++i) {
        bool someTrue = false;
        for (int j = 0; not someTrue and j < clauses[i].size(); ++j)
            someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
        if (not someTrue) {
            cout << "Error in model, clause is not satisfied:";
            for (int j = 0; j < clauses[i].size(); ++j)
                cout << clauses[i][j] << " ";
            cout << endl;
            exit(1);
        }
    }
}

void printModel() {
    cout << "--- MODEL ---" << endl;
    for (int i = 1; i <= lits.size(); ++i) {
        cout << "\t" << i << " -> " << (lits[i].value ? "TRUE" : "FALSE") << endl; 
    }
    cout << "-------------" << endl;
}


int main(int argc, char** argv) {
    readClauses(); // reads numVars, numClauses and clauses

    //model.resize(numVars+1,UNDEF);
    //indexOfNextLitToDecide = 0;
    indexOfNextLitToPropagate = 0;
    decisionLevel = 0;
    varsAssigned = 0;
    // Take care of initial unit clauses, if any
    for (uint i = 0; i < numClauses; ++i)
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = currentValueInModel(lit);
            if (val == FALSE) { cout << "UNSATISFIABLE" << endl; return 10; }
            else if (val == UNDEF) setLiteralToTrue(lit);   // and push_back in modelStack
        }

    // DPLL algorithm
    while (true) {
        while ( checkConflicts() ) {
            if (decisionLevel == 0) { cout << "UNSATISFIABLE" << endl; return 10; }
            backtrack();
        }
        int decisionLit = getNextDecisionLiteral();
        if (decisionLit == 0) { 
            //cout << "FIRST (ELEMENT): <" << heuristByAppear[0].first  << ", " << heuristByAppear[0].second << ")" << endl;
            //cout << "LAST  (ELEMENT): <" << heuristByAppear[heuristByAppear.size()-1].first  << ", " << heuristByAppear[heuristByAppear.size()-1].second << ")" << endl;
            checkmodel(); 
            cout << "SATISFIABLE" << endl;
            // Print model
            //printModel();
            return 20; 
        }
        // start new decision level:
        modelStack.push_back(0);  // push mark indicating new DL
        ++indexOfNextLitToPropagate;
        ++decisionLevel;
        setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark (modelStack)
    }
}
