#include <iostream>
#include <fstream>
#include <sstream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
//#include <queue>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

uint numVars;
uint numClauses;
vector<vector<int> > clauses;
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

void readClauses(char* input) {
    //Assume cnf size 3
    uint varPerClause = 3;

    ifstream input_file(input);
    if (input_file) {
        string str, aux;
        getline(input_file, str);
        istringstream iss(str);
        iss >> aux >> aux >> numVars >> numClauses;

        cout << "numVars: " << numVars << endl;
        cout << "numClauses: " << numClauses << endl;
        clauses.resize(numClauses);
        vector<int> numAppear(numVars+1);
        //clauses = vector<vector<int> >(numClauses, vector<int>(varPerClause));

        for (uint i = 0; i < numClauses; ++i) {
            clauses[i].resize(varPerClause);
            getline(input_file, str);
            istringstream ss(str);  //ss.str(str);
            ss >> clauses[i][0]; ++numAppear[abs(clauses[i][0])];
            ss >> clauses[i][1]; ++numAppear[abs(clauses[i][1])];
            ss >> clauses[i][2]; ++numAppear[abs(clauses[i][2])];

            //printf("\tCLAUSE[%d]: %d %d %d\n", i, clauses[i][0], clauses[i][1], clauses[i][2]);
            /*for (uint j = 0; j < varPerClause; ++i) {
            int lit;  cin >> lit;
            clauses[i][j] = lit;
            }*/
        }

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
    else { printf("couldn't open input file <%s>\n", input); exit(1); }
}


int currentValueInModel(int lit) {
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        return 1 - model[-lit];
    }
}


void setLiteralToTrue(int lit) {
    modelStack.push_back(lit);
    if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;		
}


bool propagateGivesConflict() {
    while ( indexOfNextLitToPropagate < modelStack.size() ) {
        ++indexOfNextLitToPropagate;
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
    uint i = modelStack.size() -1;
    int lit = 0;
    while (modelStack[i] != 0) { // 0 is the DL mark
        lit = modelStack[i];
        model[abs(lit)] = UNDEF;
        modelStack.pop_back();
        --i;
    }
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    indexOfNextLitToPropagate = modelStack.size();
    setLiteralToTrue(-lit);  // reverse last decision
}


// Heuristic for finding the next decision literal:
int getNextDecisionLiteral() {
    for (int i = 1; i <= numVars; ++i) {
        if (model[ heuristByAppear[i-1].second ] == UNDEF) return heuristByAppear[i-1].second;
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
    for (int i = 1; i < model.size(); ++i) {
        cout << "\t" << i << " -> " << (model[i] ? "TRUE" : "FALSE") << endl; 
    }
    cout << "-------------" << endl;
}

int main(int argc, char** argv) {
    //if (argc != 1)
    printf("INPUT: %s\n", argv[1]);
    readClauses(argv[1]); // reads numVars, numClauses and clauses

    /*for (int i = 0; i < heuristByAppear.size(); ++i) {
        cout << "#" << heuristByAppear[i].first << " <- " << heuristByAppear[i].second << endl;
    }*/

    //model = vector<int>(numVars+1, UNDEF);
    model.resize(numVars+1,UNDEF);
    indexOfNextLitToPropagate = 0;  
    decisionLevel = 0;

    // Take care of initial unit clauses, if any
    for (uint i = 0; i < numClauses; ++i)
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = currentValueInModel(lit);
            if (val == FALSE) { cout << "UNSATISFIABLE" << endl; return 10; }
            else if (val == UNDEF) setLiteralToTrue(lit);
        }

    // DPLL algorithm
    while (true) {
        while ( propagateGivesConflict() ) {
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
        setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
    }
}
