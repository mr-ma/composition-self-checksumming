#include "map"
#include "vector"
#include "list"
#include <cstdlib>
#include <stdlib.h>
#include "llvm/IR/Function.h"
#define MIN_PER_RANK 1 /* Nodes/Rank: How 'fat' the DAG should be.  */
#define MAX_PER_RANK 5
#define MIN_RANKS 3    /* Ranks: How 'tall' the DAG should be.  */
#define MAX_RANKS 5
#define PERCENT 30     /* Chance of having an Edge.  */

using namespace llvm; 
class CheckersNetwork {
	std::map<int, std::vector<int>> checkerCheckeeMap;
	void topologicalSortUtil(int v, bool visited[], std::list<int> &List);
	std::list<int> getReverseTopologicalSort();
	void printVector(std::vector<int> vector);

	public:
	void constructAcyclicCheckers(int totalNodes, int desiredConnectivity);
	std::map<Function *, std::vector<Function *>> 
		mapCheckersOnFunctions(
			const std::vector<Function *> allFunctions, 
			std::list<Function *> &reverseTopologicalSort);
};
