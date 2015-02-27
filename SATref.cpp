#include <iostream>
#include <fstream>
#include <sstream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
//#include <stack>
//#include <queue>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

class Literal
{
public:
    Literal() {
        value = UNDEF;      // model, actually
        //assigned = false;
        occurrences = 0;
    }

    int value;
    //bool assigned;
    int occurrences;
    vector<int> inClauses, negatives, positives;   // clausules on apareix el literal i-essim 
};


uint numVars;
uint numClauses;
vector<vector<int> > clauses;
//vector<int> undef_clauses;
vector<Literal> lits;

vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

vector< pair<int, int> > heuristByAppear;           // [numVars]
//priority_queue< pair<int,int> > heuristByAppear;


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
    vector<int> numAppear(numVars+1, 0);
    //undef_clauses = vector<int>(numClauses, 0);
    // Read clauses
    for (uint i = 0; i < numClauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) {
            clauses[i].push_back(lit);
            
            //++undef_clauses[i];
            ++numAppear[abs(lit)];
            ++lits[abs(lit)].occurrences;

            if (lit > 0) lits[lit].positives.push_back(i);
            else lits[abs(lit)].negatives.push_back(i);
            lits[abs(lit)].inClauses.push_back(i);
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

    // Make Heap
    heuristByAppear.resize(numVars);
    for (uint i = 1; i < numVars+1; ++i) {
        heuristByAppear[i-1] = make_pair(numAppear[i], i);
    }
    sort(heuristByAppear.begin(), heuristByAppear.end(), Comp());
    /*cout << "HEAP BEFORE" << endl;
    for (int i = 0; i < heuristByAppear.size(); ++i) {
        cout << "#" << heuristByAppear[i].first << " <- " << heuristByAppear[i].second << endl;
    }
    cout << "----------" << endl;*/
    //make_heap(heuristByAppear.begin(), heuristByAppear.end(), Comp());
}


int currentValueInModel(int lit) {
    if (lit > 0) return lits[lit].value;
    else {
        if (lits[-lit].value == UNDEF) return UNDEF;
        return 1 - lits[-lit].value;
    }

    /*if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        return 1 - model[-lit];
    }*/
}


void setLiteralToTrue(int lit) {
    modelStack.push_back(lit);
    if (lit > 0) lits[lit].value = TRUE;
    else lits[-lit].value = FALSE;

    /*if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;		*/
}


bool checkConflicts() {
    while ( indexOfNextLitToPropagate < modelStack.size() ) {
        
        cout << "--------------------" << endl;
        cout << "modelStack:";
        for (int i = 0; i < modelStack.size(); ++i) cout << " " << modelStack[i] << "(" << i << ")";
        cout << endl;
        cout << "indexOfNextLitToPropagate: " << indexOfNextLitToPropagate << endl;
        
        int var = abs(modelStack[indexOfNextLitToPropagate]);
        vector<int> clausesToCheck = lits[var].inClauses;
        
        //cout << "modelStack[indexOf]: " << modelStack[indexOfNextLitToPropagate] << endl;
        //cout << "var: " << var << endl;
        //cout << "lits[ abs(modelStack[indexOf]) ].value: " << lits[var].value << endl;
            //cout << "clausesToCheck:"; for(int k = 0; k < clausesToCheck.size(); ++k) cout << " " << clausesToCheck[k];
            //cout << endl;
                //if (lits[var].value == TRUE)        clausesToCheck = lits[var].negatives;
                //else if (lits[var].value == FALSE)  clausesToCheck = lits[var].positives;

        cout << "--------------------" << endl;

        ++indexOfNextLitToPropagate;

        /*for (int i = 0; i < clausesToCheck.size(); ++i) {
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;
            for (uint k = 0; not someLitTrue and k < clauses[ clausesToCheck[i] ].size(); ++k) {
                int val = currentValueInModel(clauses[ clausesToCheck[i] ][k]);
                if (val == TRUE) someLitTrue = true;
                else if (val == UNDEF) { ++numUndefs; lastLitUndef = clauses[ clausesToCheck[i] ][k]; }
            }
            if (not someLitTrue and numUndefs == 0) return true; // conflict! all lits false
            else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);        // modelStack.push_back()
        }*/

        for (uint i = 0; i < numClauses; ++i) {
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;
            for (uint k = 0; not someLitTrue and k < clauses[i].size(); ++k) {
                int val = currentValueInModel(clauses[i][k]);
                if (val == TRUE) someLitTrue = true;
                else if (val == UNDEF) { ++numUndefs; lastLitUndef = clauses[i][k]; }
            }
            if (not someLitTrue and numUndefs == 0) return true; // conflict! all lits false
            else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);	
        }
    }
    return false;
}


void backtrack() {
    uint i = modelStack.size() - 1;
    int lit = 0;
    while (modelStack[i] != 0) { // 0 is the DL mark
        lit = modelStack[i];
        lits[abs(lit)].value = UNDEF;
        //model[abs(lit)] = UNDEF;
        modelStack.pop_back();
        --i;
    }
    // at this point, lit is the last decision
    cout << "\t-> DL mark? :" << modelStack[modelStack.size()-1] << " size.(): " << modelStack.size() << endl;
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    indexOfNextLitToPropagate = modelStack.size();
    setLiteralToTrue(-lit);  // reverse last decision
}


// Heuristic for finding the next decision literal:
int getNextDecisionLiteral() {
    for (int i = 1; i <= numVars; ++i) {
        if (lits[ heuristByAppear[i].second ].value == UNDEF) return heuristByAppear[i].second;
    }
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

/*void update_undef(int lit) {
    for (int i = 0; i < lits[abs(lit)].inClauses; ++i) {
        --undef_clauses[ lits[abs(lit)].inClauses[i] ];
    }
}*/

int main(int argc, char** argv) {
    readClauses(); // reads numVars, numClauses and clauses

    //model.resize(numVars+1,UNDEF);
    indexOfNextLitToPropagate = 0;  
    decisionLevel = 0;

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
