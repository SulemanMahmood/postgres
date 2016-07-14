/*-------------------------------------------------------------------------
 *
 * execProcnode.c
 *	 contains dispatch functions which call the appropriate "initialize",
 *	 "get a tuple", and "cleanup" routines for the given node type.
 *	 If the node has children, then it will presumably call ExecInitNode,
 *	 ExecProcNode, or ExecEndNode on its subnodes and do the appropriate
 *	 processing.
 *
 * Portions Copyright (c) 1996-2014, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execProcnode.c
 *
 *-------------------------------------------------------------------------
 */
/*
 *	 INTERFACE ROUTINES
 *		ExecInitNode	-		initialize a plan node and its subplans
 *		ExecProcNode	-		get a tuple by executing the plan node
 *		ExecEndNode		-		shut down a plan node and its subplans
 *
 *	 NOTES
 *		This used to be three files.  It is now all combined into
 *		one file so that it is easier to keep ExecInitNode, ExecProcNode,
 *		and ExecEndNode in sync when new nodes are added.
 *
 *	 EXAMPLE
 *		Suppose we want the age of the manager of the shoe department and
 *		the number of employees in that department.  So we have the query:
 *
 *				select DEPT.no_emps, EMP.age
 *				from DEPT, EMP
 *				where EMP.name = DEPT.mgr and
 *					  DEPT.name = "shoe"
 *
 *		Suppose the planner gives us the following plan:
 *
 *						Nest Loop (DEPT.mgr = EMP.name)
 *						/		\
 *					   /		 \
 *				   Seq Scan		Seq Scan
 *					DEPT		  EMP
 *				(name = "shoe")
 *
 *		ExecutorStart() is called first.
 *		It calls InitPlan() which calls ExecInitNode() on
 *		the root of the plan -- the nest loop node.
 *
 *	  * ExecInitNode() notices that it is looking at a nest loop and
 *		as the code below demonstrates, it calls ExecInitNestLoop().
 *		Eventually this calls ExecInitNode() on the right and left subplans
 *		and so forth until the entire plan is initialized.  The result
 *		of ExecInitNode() is a plan state tree built with the same structure
 *		as the underlying plan tree.
 *
 *	  * Then when ExecutorRun() is called, it calls ExecutePlan() which calls
 *		ExecProcNode() repeatedly on the top node of the plan state tree.
 *		Each time this happens, ExecProcNode() will end up calling
 *		ExecNestLoop(), which calls ExecProcNode() on its subplans.
 *		Each of these subplans is a sequential scan so ExecSeqScan() is
 *		called.  The slots returned by ExecSeqScan() may contain
 *		tuples which contain the attributes ExecNestLoop() uses to
 *		form the tuples it returns.
 *
 *	  * Eventually ExecSeqScan() stops returning tuples and the nest
 *		loop join ends.  Lastly, ExecutorEnd() calls ExecEndNode() which
 *		calls ExecEndNestLoop() which in turn calls ExecEndNode() on
 *		its subplans which result in ExecEndSeqScan().
 *
 *		This should show how the executor works by having
 *		ExecInitNode(), ExecProcNode() and ExecEndNode() dispatch
 *		their work to the appopriate node support routines which may
 *		in turn call these routines themselves on their subplans.
 */
#include "postgres.h"

#include "executor/executor.h"
#include "executor/nodeAgg.h"
#include "executor/nodeAppend.h"
#include "executor/nodeBitmapAnd.h"
#include "executor/nodeBitmapHeapscan.h"
#include "executor/nodeBitmapIndexscan.h"
#include "executor/nodeBitmapOr.h"
#include "executor/nodeCtescan.h"
#include "executor/nodeForeignscan.h"
#include "executor/nodeFunctionscan.h"
#include "executor/nodeGroup.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "executor/nodeIndexonlyscan.h"
#include "executor/nodeIndexscan.h"
#include "executor/nodeLimit.h"
#include "executor/nodeLockRows.h"
#include "executor/nodeMaterial.h"
#include "executor/nodeMergeAppend.h"
#include "executor/nodeMergejoin.h"
#include "executor/nodeModifyTable.h"
#include "executor/nodeNestloop.h"
#include "executor/nodeRecursiveunion.h"
#include "executor/nodeResult.h"
#include "executor/nodeSeqscan.h"
#include "executor/nodeSetOp.h"
#include "executor/nodeSort.h"
#include "executor/nodeSubplan.h"
#include "executor/nodeSubqueryscan.h"
#include "executor/nodeTidscan.h"
#include "executor/nodeUnique.h"
#include "executor/nodeValuesscan.h"
#include "executor/nodeWindowAgg.h"
#include "executor/nodeWorktablescan.h"
#include "miscadmin.h"

#include "utils/rel.h"
#include "executor/tuptable.h"
#include "nodes/primnodes.h"
#include "nodes/plannodes.h"
#include <stdlib.h>
#include "./../interfaces/ecpg/include/pgtypes_numeric.h"


/* ------------------------------------------------------------------------
 *		ExecInitNode
 *
 *		Recursively initializes all the nodes in the plan tree rooted
 *		at 'node'.
 *
 *		Inputs:
 *		  'node' is the current node of the plan produced by the query planner
 *		  'estate' is the shared execution state for the plan tree
 *		  'eflags' is a bitwise OR of flag bits described in executor.h
 *
 *		Returns a PlanState node corresponding to the given Plan node.
 * ------------------------------------------------------------------------
 */
PlanState *
ExecInitNode(Plan *node, EState *estate, int eflags)
{
	PlanState  *result;
	List	   *subps;
	ListCell   *l;

	/*
	 * do nothing when we get to the end of a leaf on tree.
	 */
	if (node == NULL)
		return NULL;

	switch (nodeTag(node))
	{
			/*
			 * control nodes
			 */
		case T_Result:
			result = (PlanState *) ExecInitResult((Result *) node,
												  estate, eflags);
			{
				char str[100];
				sprintf(str, "T_Result\t");
				PrintLogs(str);

				// Print TargetList
				if (((Result *)node)->plan.targetlist != NULL){
					PrintLogs("TargetList\t");
					PrintPlan((Expr *)((Result *)node)->plan.targetlist , result, NULL);
				}
				PrintLogs("\n");
			}
			break;

		case T_ModifyTable:
			result = (PlanState *) ExecInitModifyTable((ModifyTable *) node,
													   estate, eflags);
			{
				char str[100];
				sprintf(str, "T_ModifyTable\t");
				PrintLogs(str);

				//Print Command Type
				if ( ((ModifyTable *)node)->operation == CMD_INSERT ){
					sprintf(str,"CMD_INSERT\t%s\t",((ModifyTableState *)result)->resultRelInfo->ri_RelationDesc->rd_rel->relname.data);
				}
				else if ( ((ModifyTable *)node)->operation == CMD_UPDATE ){
					sprintf(str,"CMD_UPDATE\t%s\t",((ModifyTableState *)result)->resultRelInfo->ri_RelationDesc->rd_rel->relname.data);
				}
				else if ( ((ModifyTable *)node)->operation == CMD_DELETE ){
					sprintf(str,"CMD_DELETE\t%s\t",((ModifyTableState *)result)->resultRelInfo->ri_RelationDesc->rd_rel->relname.data);
				}
				PrintLogs(str);

				PrintLogs("\n");
			}
			break;

		case T_Append:
			result = (PlanState *) ExecInitAppend((Append *) node,
												  estate, eflags);
			PrintLogs("T_Append\n");
			break;

		case T_MergeAppend:
			result = (PlanState *) ExecInitMergeAppend((MergeAppend *) node,
													   estate, eflags);
			PrintLogs("T_MergeAppend\n");
			break;

		case T_RecursiveUnion:
			result = (PlanState *) ExecInitRecursiveUnion((RecursiveUnion *) node,
														  estate, eflags);
			PrintLogs("T_RecursiveUnion\n");
			break;

		case T_BitmapAnd:
			result = (PlanState *) ExecInitBitmapAnd((BitmapAnd *) node,
													 estate, eflags);
			PrintLogs("T_BitmapAnd\n");
			break;

		case T_BitmapOr:
			result = (PlanState *) ExecInitBitmapOr((BitmapOr *) node,
													estate, eflags);
			PrintLogs("T_BitmapOr\n");
			break;

			/*
			 * scan nodes
			 */
		case T_SeqScan:
			result = (PlanState *) ExecInitSeqScan((SeqScan *) node,
												   estate, eflags);
			{
				char * table = ((SeqScanState *)result)->ss_currentRelation->rd_rel->relname.data;
				if ( (strcmp(table,"pg_type") != 0)  )
				{
					char str[100];
					sprintf(str, "T_SeqScan\t%s\t", ((SeqScanState *)result)->ss_currentRelation->rd_rel->relname.data);
					PrintLogs(str);

					// Print TargetList
					if (((SeqScan *)node)->plan.targetlist != NULL){
						PrintLogs("TargetList\t");
						PrintPlan((Expr *)((SeqScan *)node)->plan.targetlist , result, NULL);
					}

					// Print Conditions
					if (((SeqScan *)node)->plan.qual != NULL){
						PrintLogs("Conditions\t");
						PrintPlan((Expr *)((SeqScan *)node)->plan.qual, result, NULL);
					}
					PrintLogs("\n");
				}
			}
			break;

		case T_IndexScan:
			result = (PlanState *) ExecInitIndexScan((IndexScan *) node,
													 estate, eflags);
			{
				char * table = ((IndexScanState *)result)->ss.ss_currentRelation->rd_rel->relname.data;
				if ( (strcmp(table,"pg_type") != 0)  )
				{
					char str[100];
					sprintf(str, "T_IndexScan\t%s\t", ((IndexScanState *)result)->ss.ss_currentRelation->rd_rel->relname.data);
					PrintLogs(str);

					// Print TargetList
					if (((IndexScan *)node)->scan.plan.targetlist != NULL){
						PrintLogs("TargetList\t");
						PrintPlan((Expr *)((IndexScan *)node)->scan.plan.targetlist , result, NULL);
					}

					// Print Conditions
					if (((IndexScan *)node)->indexqual != NULL){
						PrintLogs("Conditions\t");
						PrintPlan((Expr *)((IndexScan *)node)->indexqual, result, NULL);
					}
					PrintLogs("\n");
				}
			}

			break;

		case T_IndexOnlyScan:
			result = (PlanState *) ExecInitIndexOnlyScan((IndexOnlyScan *) node,
														 estate, eflags);
			PrintLogs("T_IndexOnlyScan\n");
			break;

		case T_BitmapIndexScan:
			result = (PlanState *) ExecInitBitmapIndexScan((BitmapIndexScan *) node,
														   estate, eflags);
			PrintLogs("T_BitmapIndexScan\n");
			break;

		case T_BitmapHeapScan:
			result = (PlanState *) ExecInitBitmapHeapScan((BitmapHeapScan *) node,
														  estate, eflags);
			PrintLogs("T_BitmapHeapScan\n");
			break;

		case T_TidScan:
			result = (PlanState *) ExecInitTidScan((TidScan *) node,
												   estate, eflags);
			PrintLogs("T_TidScan\n");
			break;

		case T_SubqueryScan:
			result = (PlanState *) ExecInitSubqueryScan((SubqueryScan *) node,
														estate, eflags);
			PrintLogs("T_SubqueryScan\n");
			break;

		case T_FunctionScan:
			result = (PlanState *) ExecInitFunctionScan((FunctionScan *) node,
														estate, eflags);
			PrintLogs("T_FunctionScan\n");
			break;

		case T_ValuesScan:
			result = (PlanState *) ExecInitValuesScan((ValuesScan *) node,
													  estate, eflags);
			PrintLogs("T_ValuesScan\n");
			break;

		case T_CteScan:
			result = (PlanState *) ExecInitCteScan((CteScan *) node,
												   estate, eflags);
			PrintLogs("T_CteScan\n");
			break;

		case T_WorkTableScan:
			result = (PlanState *) ExecInitWorkTableScan((WorkTableScan *) node,
														 estate, eflags);
			PrintLogs("T_WorkTableScan\n");
			break;

		case T_ForeignScan:
			result = (PlanState *) ExecInitForeignScan((ForeignScan *) node,
													   estate, eflags);
			PrintLogs("T_ForeignScan\n");
			break;

			/*
			 * join nodes
			 */
		case T_NestLoop:
			result = (PlanState *) ExecInitNestLoop((NestLoop *) node,
													estate, eflags);
			{
				char str[100];
				NestLoop * PlannedStateNode = (NestLoop *)node;
				sprintf(str, "T_NestLoop\t");
				PrintLogs(str);

				// Print Join Type
				switch (PlannedStateNode->join.jointype){
					case JOIN_INNER:
						sprintf(str,"JOIN_INNER\t");
						break;
					case JOIN_SEMI:
						sprintf(str,"JOIN_SEMI\t");
						break;
					case JOIN_LEFT:
						sprintf(str,"JOIN_LEFT\t");
						break;
					case JOIN_ANTI:
						sprintf(str,"JOIN_ANTI\t");
						break;
					case JOIN_RIGHT:
						sprintf(str,"JOIN_RIGHT\t");
						break;
					case JOIN_FULL:
						sprintf(str,"JOIN_FULL\t");
						break;
					default:
						sprintf(str,"Invalid\t");

				}
				PrintLogs(str);

				// Print TargetList
				if (PlannedStateNode->join.plan.targetlist != NULL){
					PrintLogs("TargetList\t");
					PrintPlan((Expr *)PlannedStateNode->join.plan.targetlist , result, NULL);
				}

				// Print Conditions
				if (PlannedStateNode->join.joinqual != NULL){
					PrintLogs("Conditions\t");
					PrintPlan((Expr *)PlannedStateNode->join.joinqual , result, NULL);
				}
				PrintLogs("\n");
			}
			break;

		case T_MergeJoin:
			result = (PlanState *) ExecInitMergeJoin((MergeJoin *) node,
													 estate, eflags);
			{
				char str[100];
				MergeJoin * PlannedStateNode = (MergeJoin *)node;
				sprintf(str, "T_MergeJoin\t");
				PrintLogs(str);

				// Print Join Type
				switch (PlannedStateNode->join.jointype){
					case JOIN_INNER:
						sprintf(str,"JOIN_INNER\t");
						break;
					case JOIN_SEMI:
						sprintf(str,"JOIN_SEMI\t");
						break;
					case JOIN_LEFT:
						sprintf(str,"JOIN_LEFT\t");
						break;
					case JOIN_ANTI:
						sprintf(str,"JOIN_ANTI\t");
						break;
					case JOIN_RIGHT:
						sprintf(str,"JOIN_RIGHT\t");
						break;
					case JOIN_FULL:
						sprintf(str,"JOIN_FULL\t");
						break;
					default:
						sprintf(str,"Invalid\t");

				}
				PrintLogs(str);

				// Print TargetList
				if (PlannedStateNode->join.plan.targetlist != NULL){
					PrintLogs("TargetList\t");
					PrintPlan((Expr *)PlannedStateNode->join.plan.targetlist , result, NULL);
				}

				// Print Conditions
				if (PlannedStateNode->mergeclauses != NULL){
					PrintLogs("Conditions\t");
					PrintPlan((Expr *)PlannedStateNode->mergeclauses , result, NULL);
				}
				PrintLogs("\n");
			}
			break;

		case T_HashJoin:
			result = (PlanState *) ExecInitHashJoin((HashJoin *) node,
													estate, eflags);

			{
				char str[100];
				HashJoin * PlannedStateNode = (HashJoin *)node;
				sprintf(str, "T_HashJoin\t");
				PrintLogs(str);

				// Print Join Type
				switch (PlannedStateNode->join.jointype){
					case JOIN_INNER:
						sprintf(str,"JOIN_INNER\t");
						break;
					case JOIN_SEMI:
						sprintf(str,"JOIN_SEMI\t");
						break;
					case JOIN_LEFT:
						sprintf(str,"JOIN_LEFT\t");
						break;
					case JOIN_ANTI:
						sprintf(str,"JOIN_ANTI\t");
						break;
					case JOIN_RIGHT:
						sprintf(str,"JOIN_RIGHT\t");
						break;
					case JOIN_FULL:
						sprintf(str,"JOIN_FULL\t");
						break;
					default:
						sprintf(str,"Invalid\t");

				}
				PrintLogs(str);

				// Print TargetList
				if (PlannedStateNode->join.plan.targetlist != NULL){
					PrintLogs("TargetList\t");
					PrintPlan((Expr *)PlannedStateNode->join.plan.targetlist , result, NULL);
				}

				// Print Conditions
				if (PlannedStateNode->hashclauses != NULL){
					PrintLogs("Conditions\t");
					PrintPlan((Expr *)PlannedStateNode->hashclauses , result, NULL);
				}
				PrintLogs("\n");
			}

			break;

			/*
			 * materialization nodes
			 */
		case T_Material:
			result = (PlanState *) ExecInitMaterial((Material *) node,
													estate, eflags);
			PrintLogs("T_Material\n");
			break;

		case T_Sort:
			result = (PlanState *) ExecInitSort((Sort *) node,
												estate, eflags);
			PrintLogs("T_Sort\n");
			break;

		case T_Group:
			result = (PlanState *) ExecInitGroup((Group *) node,
												 estate, eflags);
			PrintLogs("T_Group\n");
			break;

		case T_Agg:
			result = (PlanState *) ExecInitAgg((Agg *) node,
											   estate, eflags);
			PrintLogs("T_Agg\n");
			break;

		case T_WindowAgg:
			result = (PlanState *) ExecInitWindowAgg((WindowAgg *) node,
													 estate, eflags);
			PrintLogs("T_WindowAgg\n");
			break;

		case T_Unique:
			result = (PlanState *) ExecInitUnique((Unique *) node,
												  estate, eflags);
			PrintLogs("T_Unique\n");
			break;

		case T_Hash:
			result = (PlanState *) ExecInitHash((Hash *) node,
												estate, eflags);
			PrintLogs("T_Hash\n");
			break;

		case T_SetOp:
			result = (PlanState *) ExecInitSetOp((SetOp *) node,
												 estate, eflags);
			PrintLogs("T_SetOp\n");
			break;

		case T_LockRows:
			result = (PlanState *) ExecInitLockRows((LockRows *) node,
													estate, eflags);
			PrintLogs("T_LockRows\n");
			break;

		case T_Limit:
			result = (PlanState *) ExecInitLimit((Limit *) node,
												 estate, eflags);
			PrintLogs("T_Limit\n");
			break;

		default:
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
			result = NULL;		/* keep compiler quiet */
			break;
	}

	/*
	 * Initialize any initPlans present in this node.  The planner put them in
	 * a separate list for us.
	 */
	subps = NIL;
	foreach(l, node->initPlan)
	{
		SubPlan    *subplan = (SubPlan *) lfirst(l);
		SubPlanState *sstate;

		Assert(IsA(subplan, SubPlan));
		sstate = ExecInitSubPlan(subplan, result);
		subps = lappend(subps, sstate);
	}
	result->initPlan = subps;

	/* Set up instrumentation for this node if requested */
	if (estate->es_instrument)
		result->instrument = InstrAlloc(1, estate->es_instrument);

	return result;
}


/* ----------------------------------------------------------------
 *		ExecProcNode
 *
 *		Execute the given node to return a(nother) tuple.
 * ----------------------------------------------------------------
 */
TupleTableSlot *
ExecProcNode(PlanState *node)
{
	TupleTableSlot *result;

	CHECK_FOR_INTERRUPTS();

	if (node->chgParam != NULL) /* something changed */
		ExecReScan(node);		/* let ReScan handle this */

	if (node->instrument)
		InstrStartNode(node->instrument);

	switch (nodeTag(node))
	{
			/*
			 * control nodes
			 */
		case T_ResultState:
			result = ExecResult((ResultState *) node);
			break;

		case T_ModifyTableState:
			result = ExecModifyTable((ModifyTableState *) node);
			break;

		case T_AppendState:
			result = ExecAppend((AppendState *) node);
			break;

		case T_MergeAppendState:
			result = ExecMergeAppend((MergeAppendState *) node);
			break;

		case T_RecursiveUnionState:
			result = ExecRecursiveUnion((RecursiveUnionState *) node);
			break;

			/* BitmapAndState does not yield tuples */

			/* BitmapOrState does not yield tuples */

			/*
			 * scan nodes
			 */
		case T_SeqScanState:
			result = ExecSeqScan((SeqScanState *) node);
			break;

		case T_IndexScanState:
			result = ExecIndexScan((IndexScanState *) node);
			break;

		case T_IndexOnlyScanState:
			result = ExecIndexOnlyScan((IndexOnlyScanState *) node);
			break;

			/* BitmapIndexScanState does not yield tuples */

		case T_BitmapHeapScanState:
			result = ExecBitmapHeapScan((BitmapHeapScanState *) node);
			break;

		case T_TidScanState:
			result = ExecTidScan((TidScanState *) node);
			break;

		case T_SubqueryScanState:
			result = ExecSubqueryScan((SubqueryScanState *) node);
			break;

		case T_FunctionScanState:
			result = ExecFunctionScan((FunctionScanState *) node);
			break;

		case T_ValuesScanState:
			result = ExecValuesScan((ValuesScanState *) node);
			break;

		case T_CteScanState:
			result = ExecCteScan((CteScanState *) node);
			break;

		case T_WorkTableScanState:
			result = ExecWorkTableScan((WorkTableScanState *) node);
			break;

		case T_ForeignScanState:
			result = ExecForeignScan((ForeignScanState *) node);
			break;

			/*
			 * join nodes
			 */
		case T_NestLoopState:
			result = ExecNestLoop((NestLoopState *) node);
			break;

		case T_MergeJoinState:
			result = ExecMergeJoin((MergeJoinState *) node);
			break;

		case T_HashJoinState:
			result = ExecHashJoin((HashJoinState *) node);
			break;

			/*
			 * materialization nodes
			 */
		case T_MaterialState:
			result = ExecMaterial((MaterialState *) node);
			break;

		case T_SortState:
			result = ExecSort((SortState *) node);
			break;

		case T_GroupState:
			result = ExecGroup((GroupState *) node);
			break;

		case T_AggState:
			result = ExecAgg((AggState *) node);
			break;

		case T_WindowAggState:
			result = ExecWindowAgg((WindowAggState *) node);
			break;

		case T_UniqueState:
			result = ExecUnique((UniqueState *) node);
			break;

		case T_HashState:
			result = ExecHash((HashState *) node);
			break;

		case T_SetOpState:
			result = ExecSetOp((SetOpState *) node);
			break;

		case T_LockRowsState:
			result = ExecLockRows((LockRowsState *) node);
			break;

		case T_LimitState:
			result = ExecLimit((LimitState *) node);
			break;

		default:
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
			result = NULL;
			break;
	}

	if (node->instrument)
		InstrStopNode(node->instrument, TupIsNull(result) ? 0.0 : 1.0);

	return result;
}


/* ----------------------------------------------------------------
 *		MultiExecProcNode
 *
 *		Execute a node that doesn't return individual tuples
 *		(it might return a hashtable, bitmap, etc).  Caller should
 *		check it got back the expected kind of Node.
 *
 * This has essentially the same responsibilities as ExecProcNode,
 * but it does not do InstrStartNode/InstrStopNode (mainly because
 * it can't tell how many returned tuples to count).  Each per-node
 * function must provide its own instrumentation support.
 * ----------------------------------------------------------------
 */
Node *
MultiExecProcNode(PlanState *node)
{
	Node	   *result;

	CHECK_FOR_INTERRUPTS();

	if (node->chgParam != NULL) /* something changed */
		ExecReScan(node);		/* let ReScan handle this */

	switch (nodeTag(node))
	{
			/*
			 * Only node types that actually support multiexec will be listed
			 */

		case T_HashState:
			result = MultiExecHash((HashState *) node);
			break;

		case T_BitmapIndexScanState:
			result = MultiExecBitmapIndexScan((BitmapIndexScanState *) node);
			break;

		case T_BitmapAndState:
			result = MultiExecBitmapAnd((BitmapAndState *) node);
			break;

		case T_BitmapOrState:
			result = MultiExecBitmapOr((BitmapOrState *) node);
			break;

		default:
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
			result = NULL;
			break;
	}

	return result;
}


/* ----------------------------------------------------------------
 *		ExecEndNode
 *
 *		Recursively cleans up all the nodes in the plan rooted
 *		at 'node'.
 *
 *		After this operation, the query plan will not be able to be
 *		processed any further.  This should be called only after
 *		the query plan has been fully executed.
 * ----------------------------------------------------------------
 */
void
ExecEndNode(PlanState *node)
{
	/*
	 * do nothing when we get to the end of a leaf on tree.
	 */
	if (node == NULL)
		return;

	if (node->chgParam != NULL)
	{
		bms_free(node->chgParam);
		node->chgParam = NULL;
	}

	switch (nodeTag(node))
	{
			/*
			 * control nodes
			 */
		case T_ResultState:
			ExecEndResult((ResultState *) node);
			break;

		case T_ModifyTableState:
			ExecEndModifyTable((ModifyTableState *) node);
			break;

		case T_AppendState:
			ExecEndAppend((AppendState *) node);
			break;

		case T_MergeAppendState:
			ExecEndMergeAppend((MergeAppendState *) node);
			break;

		case T_RecursiveUnionState:
			ExecEndRecursiveUnion((RecursiveUnionState *) node);
			break;

		case T_BitmapAndState:
			ExecEndBitmapAnd((BitmapAndState *) node);
			break;

		case T_BitmapOrState:
			ExecEndBitmapOr((BitmapOrState *) node);
			break;

			/*
			 * scan nodes
			 */
		case T_SeqScanState:
			ExecEndSeqScan((SeqScanState *) node);
			break;

		case T_IndexScanState:
			ExecEndIndexScan((IndexScanState *) node);
			break;

		case T_IndexOnlyScanState:
			ExecEndIndexOnlyScan((IndexOnlyScanState *) node);
			break;

		case T_BitmapIndexScanState:
			ExecEndBitmapIndexScan((BitmapIndexScanState *) node);
			break;

		case T_BitmapHeapScanState:
			ExecEndBitmapHeapScan((BitmapHeapScanState *) node);
			break;

		case T_TidScanState:
			ExecEndTidScan((TidScanState *) node);
			break;

		case T_SubqueryScanState:
			ExecEndSubqueryScan((SubqueryScanState *) node);
			break;

		case T_FunctionScanState:
			ExecEndFunctionScan((FunctionScanState *) node);
			break;

		case T_ValuesScanState:
			ExecEndValuesScan((ValuesScanState *) node);
			break;

		case T_CteScanState:
			ExecEndCteScan((CteScanState *) node);
			break;

		case T_WorkTableScanState:
			ExecEndWorkTableScan((WorkTableScanState *) node);
			break;

		case T_ForeignScanState:
			ExecEndForeignScan((ForeignScanState *) node);
			break;

			/*
			 * join nodes
			 */
		case T_NestLoopState:
			ExecEndNestLoop((NestLoopState *) node);
			break;

		case T_MergeJoinState:
			ExecEndMergeJoin((MergeJoinState *) node);
			break;

		case T_HashJoinState:
			ExecEndHashJoin((HashJoinState *) node);
			break;

			/*
			 * materialization nodes
			 */
		case T_MaterialState:
			ExecEndMaterial((MaterialState *) node);
			break;

		case T_SortState:
			ExecEndSort((SortState *) node);
			break;

		case T_GroupState:
			ExecEndGroup((GroupState *) node);
			break;

		case T_AggState:
			ExecEndAgg((AggState *) node);
			break;

		case T_WindowAggState:
			ExecEndWindowAgg((WindowAggState *) node);
			break;

		case T_UniqueState:
			ExecEndUnique((UniqueState *) node);
			break;

		case T_HashState:
			ExecEndHash((HashState *) node);
			break;

		case T_SetOpState:
			ExecEndSetOp((SetOpState *) node);
			break;

		case T_LockRowsState:
			ExecEndLockRows((LockRowsState *) node);
			break;

		case T_LimitState:
			ExecEndLimit((LimitState *) node);
			break;

		default:
			elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
			break;
	}
}


void PrintPlan(Expr *node, PlanState *parent, PLpgSQL_execstate * estate)
{
	if (node == NULL)
		return;

	switch (nodeTag(node))
	{
		case T_Var:
			/* varattno == InvalidAttrNumber means it's a whole-row Var */
			if (((Var *) node)->varattno == InvalidAttrNumber) {

			}
			else {
				char str[100];
				if (((Var *) node)->varattno > 0){
					if (parent->type == T_SeqScanState){
						sprintf(str,"Col %s\t", (((SeqScanState *)parent)->ss_ScanTupleSlot->tts_tupleDescriptor->attrs[(((Var *) node)->varattno)-1])->attname.data );
					}
					else if (parent->type == T_IndexScanState ){
						sprintf(str,"Col %s\t", (((IndexScanState *)parent)->ss.ss_ScanTupleSlot->tts_tupleDescriptor->attrs[(((Var *) node)->varattno)-1])->attname.data );
					}
					else if (parent->type == T_HashJoinState || parent->type == T_MergeJoinState || parent->type == T_NestLoopState ){
						Var * Variable = (Var *)node;
						if (Variable->varno == INNER_VAR){
							sprintf(str,"Col INNER.%d\t", (Variable->varattno) - 1);
						}
						else if (Variable->varno == OUTER_VAR){
							sprintf(str,"Col OUTER.%d\t", (Variable->varattno) - 1);
						}
					}
				}
				else if (((Var *) node)->varattno == -1){
					sprintf(str,"Col ctid\t");
				}
				PrintLogs(str);
			}
			break;
		case T_Const:
			{
				char str[200];
				int i;
				for (i = 0; i < 200; i++){
					str[i] = '\0';
				}

				if ( (((Const *)node)->location == -1) && ((Const *)node)->paramid >=1){
					if (parent->type == T_SeqScanState ){
						ParamListInfo params =  ((SeqScanState*) parent)->ps.ps_ExprContext->ecxt_param_list_info;
						if (params != NULL){
							if (params->paramFetchArg != NULL){
								sprintf(str,"Param %s\t", ((PLpgSQL_var *)(((PLpgSQL_execstate *)(params->paramFetchArg))->datums[((Const *)node)->paramid - 1]))->refname);
							}
						}
					}
					else if (parent->type == T_IndexScanState ){
						ParamListInfo params =  ((IndexScanState*) parent)->ss.ps.ps_ExprContext->ecxt_param_list_info;
						if (params != NULL){
							if (params->paramFetchArg != NULL){
								sprintf(str,"Param %s\t", ((PLpgSQL_var *)(((PLpgSQL_execstate *)(params->paramFetchArg))->datums[((Const *)node)->paramid - 1]))->refname);
							}
						}
					}
					else if (parent->type == T_ResultState ){
						ParamListInfo params =  ((ResultState *) parent)->ps.ps_ExprContext->ecxt_param_list_info;
						if (params != NULL){
							if (params->paramFetchArg != NULL){
								sprintf(str,"Param %s\t", ((PLpgSQL_var *)(((PLpgSQL_execstate *)(params->paramFetchArg))->datums[((Const *)node)->paramid - 1]))->refname);
							}
						}
					}
				}
				else if (((Const *)node)->constisnull){
					sprintf(str,"NULL\t");
				}
				else{
					Const * Constant = (Const *)node;
					if (Constant->consttype >=20 && Constant->consttype <=23){  // Integer
						sprintf(str,"%d %d\t", Constant->consttype, (int)(Constant->constvalue));
					}
					else if (Constant->consttype == 16){		// Boolean
						if (Constant->constvalue == 1){
							sprintf(str,"%d %s\t", Constant->consttype, "True");
						}
						else{
							sprintf(str,"%d %s\t", Constant->consttype, "False");
						}
					}
					else if (Constant->consttype == 25){
						text * ConstString = (text *)(Constant->constvalue);
						char value[100];
						i = 0;
						while ((ConstString->vl_dat)[i] != '~'){
							value[i] = (ConstString->vl_dat)[i];
							i++;
							if (i == 99){
								break;
							}
						}
						value[i] = '\0';
						sprintf(str,"%d %s\t", Constant->consttype,value);
					}
					else{
						sprintf(str, "%d NotImplemented\t", Constant->consttype);
					}
				}

				PrintLogs(str);
			}
			break;
		case T_Param:
			switch (((Param *) node)->paramkind)
			{
				char str[100];

				case PARAM_EXEC:
					if (parent != NULL){
						if ((parent->ps_ExprContext->ecxt_param_exec_vals[((Param *) node)->paramid]).value == 0){
							sprintf(str, "%d %s", 16, "False");
						}
						else{
							sprintf(str, "%d %s", 16, "True");
						}

						PrintLogs(str);
					}
					break;
				case PARAM_EXTERN:
					{
						if (((Param *)node)->paramid >= 1){
							if (parent == NULL){
								sprintf(str,"Param %s\t", ((PLpgSQL_var *)(estate->datums[((Param *)node)->paramid - 1]))->refname);
							}
							else if (parent->type == T_SeqScanState ){
								ParamListInfo params =  ((SeqScanState*) parent)->ps.ps_ExprContext->ecxt_param_list_info;
								if (params != NULL){
									if (params->paramFetchArg != NULL){
										sprintf(str,"Param %s\t", ((PLpgSQL_var *)(((PLpgSQL_execstate *)(params->paramFetchArg))->datums[((Param *)node)->paramid - 1]))->refname);
									}
								}
							}
							else if (parent->type == T_IndexScanState ){
								ParamListInfo params =  ((IndexScanState*) parent)->ss.ps.ps_ExprContext->ecxt_param_list_info;
								if (params != NULL){
									if (params->paramFetchArg != NULL){
										sprintf(str,"Param %s\t", ((PLpgSQL_var *)(((PLpgSQL_execstate *)(params->paramFetchArg))->datums[((Param *)node)->paramid - 1]))->refname);
									}
								}
							}
							else if (parent->type == T_ResultState ){
								ParamListInfo params =  ((ResultState *) parent)->ps.ps_ExprContext->ecxt_param_list_info;
								if (params != NULL){
									if (params->paramFetchArg != NULL){
										sprintf(str,"Param %s\t", ((PLpgSQL_var *)(((PLpgSQL_execstate *)(params->paramFetchArg))->datums[((Param *)node)->paramid - 1]))->refname);
									}
								}
							}
						}
						PrintLogs(str);
					}
					break;
				default:
					break;
			}
			break;
		case T_CoerceToDomainValue:
			PrintLogs("T_CoerceToDomainValue\t");
//			state = (ExprState *) makeNode(ExprState);
//			state->evalfunc = ExecEvalCoerceToDomainValue;
			break;
		case T_CaseTestExpr:
			PrintLogs("T_CaseTestExpr\t");
//			state = (ExprState *) makeNode(ExprState);
//			state->evalfunc = ExecEvalCaseTestExpr;
			break;
		case T_Aggref:
			PrintLogs("T_Aggref\t");
//			{
//				Aggref	   *aggref = (Aggref *) node;
//				AggrefExprState *astate = makeNode(AggrefExprState);
//
//				astate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalAggref;
//				if (parent && IsA(parent, AggState))
//				{
//					AggState   *aggstate = (AggState *) parent;
//					int			naggs;
//
//					aggstate->aggs = lcons(astate, aggstate->aggs);
//					naggs = ++aggstate->numaggs;
//
//					astate->aggdirectargs = (List *) ExecInitExpr((Expr *) aggref->aggdirectargs,
//																  parent);
//					astate->args = (List *) ExecInitExpr((Expr *) aggref->args,
//														 parent);
//					astate->aggfilter = ExecInitExpr(aggref->aggfilter,
//													 parent);
//
//					/*
//					 * Complain if the aggregate's arguments contain any
//					 * aggregates; nested agg functions are semantically
//					 * nonsensical.  (This should have been caught earlier,
//					 * but we defend against it here anyway.)
//					 */
//					if (naggs != aggstate->numaggs)
//						ereport(ERROR,
//								(errcode(ERRCODE_GROUPING_ERROR),
//						errmsg("aggregate function calls cannot be nested")));
//				}
//				else
//				{
//					/* planner messed up */
//					elog(ERROR, "Aggref found in non-Agg plan node");
//				}
//				state = (ExprState *) astate;
//			}
			break;
		case T_WindowFunc:
			PrintLogs("T_WindowFunc\t");
//			{
//				WindowFunc *wfunc = (WindowFunc *) node;
//				WindowFuncExprState *wfstate = makeNode(WindowFuncExprState);
//
//				wfstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalWindowFunc;
//				if (parent && IsA(parent, WindowAggState))
//				{
//					WindowAggState *winstate = (WindowAggState *) parent;
//					int			nfuncs;
//
//					winstate->funcs = lcons(wfstate, winstate->funcs);
//					nfuncs = ++winstate->numfuncs;
//					if (wfunc->winagg)
//						winstate->numaggs++;
//
//					wfstate->args = (List *) ExecInitExpr((Expr *) wfunc->args,
//														  parent);
//					wfstate->aggfilter = ExecInitExpr(wfunc->aggfilter,
//													  parent);
//
//					/*
//					 * Complain if the windowfunc's arguments contain any
//					 * windowfuncs; nested window functions are semantically
//					 * nonsensical.  (This should have been caught earlier,
//					 * but we defend against it here anyway.)
//					 */
//					if (nfuncs != winstate->numfuncs)
//						ereport(ERROR,
//								(errcode(ERRCODE_WINDOWING_ERROR),
//						  errmsg("window function calls cannot be nested")));
//				}
//				else
//				{
//					/* planner messed up */
//					elog(ERROR, "WindowFunc found in non-WindowAgg plan node");
//				}
//				state = (ExprState *) wfstate;
//			}
			break;
		case T_ArrayRef:
			PrintLogs("T_ArrayRef\t");
//			{
//				ArrayRef   *aref = (ArrayRef *) node;
//				ArrayRefExprState *astate = makeNode(ArrayRefExprState);
//
//				astate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalArrayRef;
//				astate->refupperindexpr = (List *)
//					ExecInitExpr((Expr *) aref->refupperindexpr, parent);
//				astate->reflowerindexpr = (List *)
//					ExecInitExpr((Expr *) aref->reflowerindexpr, parent);
//				astate->refexpr = ExecInitExpr(aref->refexpr, parent);
//				astate->refassgnexpr = ExecInitExpr(aref->refassgnexpr,
//													parent);
//				/* do one-time catalog lookups for type info */
//				astate->refattrlength = get_typlen(aref->refarraytype);
//				get_typlenbyvalalign(aref->refelemtype,
//									 &astate->refelemlength,
//									 &astate->refelembyval,
//									 &astate->refelemalign);
//				state = (ExprState *) astate;
//			}
			break;
		case T_FuncExpr:
			{
				FuncExpr   *funcexpr = (FuncExpr *) node;

				PrintLogs("FunctionCall\t");
				PrintPlan((Expr *) funcexpr->args, parent, estate);
			}
			break;
		case T_OpExpr:
			{
				OpExpr	   *opexpr = (OpExpr *) node;
				if (opexpr->opfuncid == 65 || opexpr->opfuncid == 67){
					PrintLogs("=\t");
				}
				else if (opexpr->opfuncid == 66){
					PrintLogs("<\t");
				}
				else if (opexpr->opfuncid == 141){
					PrintLogs("*\t");
				}
				else if (opexpr->opfuncid == 144){
					PrintLogs("!=\t");
				}
				else if (opexpr->opfuncid == 147){
					PrintLogs(">\t");
				}
				else if (opexpr->opfuncid == 149){
					PrintLogs("<=\t");
				}
				else if (opexpr->opfuncid == 150){
					PrintLogs(">=\t");
				}
				else if (opexpr->opfuncid == 154){
					PrintLogs("/\t");
				}
				else if (opexpr->opfuncid == 177){
					PrintLogs("+\t");
				}
				else if (opexpr->opfuncid == 181){
					PrintLogs("-\t");
				}
				else{
					char str[100];
					sprintf(str,"***%d\t",opexpr->opfuncid);
					PrintLogs(str);
				}
				PrintPlan((Expr *) opexpr->args, parent, estate);
			}
			break;
		case T_DistinctExpr:
			PrintLogs("T_DistinctExpr\t");
//			{
//				DistinctExpr *distinctexpr = (DistinctExpr *) node;
//				FuncExprState *fstate = makeNode(FuncExprState);
//
//				fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalDistinct;
//				fstate->args = (List *)
//					ExecInitExpr((Expr *) distinctexpr->args, parent);
//				fstate->func.fn_oid = InvalidOid;		/* not initialized */
//				state = (ExprState *) fstate;
//			}
			break;
		case T_NullIfExpr:
			PrintLogs("T_NullIfExpr\t");
//			{
//				NullIfExpr *nullifexpr = (NullIfExpr *) node;
//				FuncExprState *fstate = makeNode(FuncExprState);
//
//				fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalNullIf;
//				fstate->args = (List *)
//					ExecInitExpr((Expr *) nullifexpr->args, parent);
//				fstate->func.fn_oid = InvalidOid;		/* not initialized */
//				state = (ExprState *) fstate;
//			}
//			break;
		case T_ScalarArrayOpExpr:
			{
				ScalarArrayOpExpr *opexpr = (ScalarArrayOpExpr *) node;
				if (opexpr->opfuncid == 65 || opexpr->opfuncid == 67){
					PrintLogs("A=\t");
				}
				else{
					char str[100];
					sprintf(str,"***%d\t",opexpr->opfuncid);
					PrintLogs(str);
				}

				PrintPlan((Expr *) opexpr->args, parent, estate);
			}
			break;
		case T_BoolExpr:
			{
				BoolExpr   *boolexpr = (BoolExpr *) node;

				switch (boolexpr->boolop)
				{
					case AND_EXPR:
						PrintLogs("AND\t");
						break;
					case OR_EXPR:
						PrintLogs("OR\t");
						break;
					case NOT_EXPR:
						PrintLogs("Not\t");
						break;
					default:
						break;
				}
				PrintPlan((Expr *) boolexpr->args, parent, estate);
			}
			break;
		case T_SubPlan:
			PrintLogs("T_SubPlan\t");
//			{
//				SubPlan    *subplan = (SubPlan *) node;
//				SubPlanState *sstate;
//
//				if (!parent)
//					elog(ERROR, "SubPlan found with no parent plan");
//
//				sstate = ExecInitSubPlan(subplan, parent);
//
//				/* Add SubPlanState nodes to parent->subPlan */
//				parent->subPlan = lappend(parent->subPlan, sstate);
//
//				state = (ExprState *) sstate;
//			}
			break;
		case T_AlternativeSubPlan:
			PrintLogs("T_AlternativeSubPlan\t");
//			{
//				AlternativeSubPlan *asplan = (AlternativeSubPlan *) node;
//				AlternativeSubPlanState *asstate;
//
//				if (!parent)
//					elog(ERROR, "AlternativeSubPlan found with no parent plan");
//
//				asstate = ExecInitAlternativeSubPlan(asplan, parent);
//
//				state = (ExprState *) asstate;
//			}
			break;
		case T_FieldSelect:
			PrintLogs("T_FieldSelect\t");
//			{
//				FieldSelect *fselect = (FieldSelect *) node;
//				FieldSelectState *fstate = makeNode(FieldSelectState);
//
//				fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFieldSelect;
//				fstate->arg = ExecInitExpr(fselect->arg, parent);
//				fstate->argdesc = NULL;
//				state = (ExprState *) fstate;
//			}
			break;
		case T_FieldStore:
			PrintLogs("T_FieldStore\t");
//			{
//				FieldStore *fstore = (FieldStore *) node;
//				FieldStoreState *fstate = makeNode(FieldStoreState);
//
//				fstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalFieldStore;
//				fstate->arg = ExecInitExpr(fstore->arg, parent);
//				fstate->newvals = (List *) ExecInitExpr((Expr *) fstore->newvals, parent);
//				fstate->argdesc = NULL;
//				state = (ExprState *) fstate;
//			}
			break;
		case T_RelabelType:
			PrintLogs("T_RelabelType\t");
//			{
//				RelabelType *relabel = (RelabelType *) node;
//				GenericExprState *gstate = makeNode(GenericExprState);
//
//				gstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalRelabelType;
//				gstate->arg = ExecInitExpr(relabel->arg, parent);
//				state = (ExprState *) gstate;
//			}
			break;
		case T_CoerceViaIO:
			PrintLogs("T_CoerceViaIO\t");
//			{
//				CoerceViaIO *iocoerce = (CoerceViaIO *) node;
//				CoerceViaIOState *iostate = makeNode(CoerceViaIOState);
//				Oid			iofunc;
//				bool		typisvarlena;
//
//				iostate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalCoerceViaIO;
//				iostate->arg = ExecInitExpr(iocoerce->arg, parent);
//				/* lookup the result type's input function */
//				getTypeInputInfo(iocoerce->resulttype, &iofunc,
//								 &iostate->intypioparam);
//				fmgr_info(iofunc, &iostate->infunc);
//				/* lookup the input type's output function */
//				getTypeOutputInfo(exprType((Node *) iocoerce->arg),
//								  &iofunc, &typisvarlena);
//				fmgr_info(iofunc, &iostate->outfunc);
//				state = (ExprState *) iostate;
//			}
			break;
		case T_ArrayCoerceExpr:
			PrintLogs("T_ArrayCoerceExpr\t");
//			{
//				ArrayCoerceExpr *acoerce = (ArrayCoerceExpr *) node;
//				ArrayCoerceExprState *astate = makeNode(ArrayCoerceExprState);
//
//				astate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalArrayCoerceExpr;
//				astate->arg = ExecInitExpr(acoerce->arg, parent);
//				astate->resultelemtype = get_element_type(acoerce->resulttype);
//				if (astate->resultelemtype == InvalidOid)
//					ereport(ERROR,
//							(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
//							 errmsg("target type is not an array")));
//				/* Arrays over domains aren't supported yet */
//				Assert(getBaseType(astate->resultelemtype) ==
//					   astate->resultelemtype);
//				astate->elemfunc.fn_oid = InvalidOid;	/* not initialized */
//				astate->amstate = (ArrayMapState *) palloc0(sizeof(ArrayMapState));
//				state = (ExprState *) astate;
//			}
			break;
		case T_ConvertRowtypeExpr:
			PrintLogs("T_ConvertRowtypeExpr\t");
//			{
//				ConvertRowtypeExpr *convert = (ConvertRowtypeExpr *) node;
//				ConvertRowtypeExprState *cstate = makeNode(ConvertRowtypeExprState);
//
//				cstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalConvertRowtype;
//				cstate->arg = ExecInitExpr(convert->arg, parent);
//				state = (ExprState *) cstate;
//			}
//			break;
		case T_CaseExpr:
			PrintLogs("T_CaseExpr\t");
//			{
//				CaseExpr   *caseexpr = (CaseExpr *) node;
//				CaseExprState *cstate = makeNode(CaseExprState);
//				List	   *outlist = NIL;
//				ListCell   *l;
//
//				cstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalCase;
//				cstate->arg = ExecInitExpr(caseexpr->arg, parent);
//				foreach(l, caseexpr->args)
//				{
//					CaseWhen   *when = (CaseWhen *) lfirst(l);
//					CaseWhenState *wstate = makeNode(CaseWhenState);
//
//					Assert(IsA(when, CaseWhen));
//					wstate->xprstate.evalfunc = NULL;	/* not used */
//					wstate->xprstate.expr = (Expr *) when;
//					wstate->expr = ExecInitExpr(when->expr, parent);
//					wstate->result = ExecInitExpr(when->result, parent);
//					outlist = lappend(outlist, wstate);
//				}
//				cstate->args = outlist;
//				cstate->defresult = ExecInitExpr(caseexpr->defresult, parent);
//				state = (ExprState *) cstate;
//			}
			break;
		case T_ArrayExpr:
			PrintLogs("T_ArrayExpr\t");
//			{
//				ArrayExpr  *arrayexpr = (ArrayExpr *) node;
//				ArrayExprState *astate = makeNode(ArrayExprState);
//				List	   *outlist = NIL;
//				ListCell   *l;
//
//				astate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalArray;
//				foreach(l, arrayexpr->elements)
//				{
//					Expr	   *e = (Expr *) lfirst(l);
//					ExprState  *estate;
//
//					estate = ExecInitExpr(e, parent);
//					outlist = lappend(outlist, estate);
//				}
//				astate->elements = outlist;
//				/* do one-time catalog lookup for type info */
//				get_typlenbyvalalign(arrayexpr->element_typeid,
//									 &astate->elemlength,
//									 &astate->elembyval,
//									 &astate->elemalign);
//				state = (ExprState *) astate;
//			}
			break;
		case T_RowExpr:
			PrintLogs("T_RowExpr\t");
//			{
//				RowExpr    *rowexpr = (RowExpr *) node;
//				RowExprState *rstate = makeNode(RowExprState);
//				Form_pg_attribute *attrs;
//				List	   *outlist = NIL;
//				ListCell   *l;
//				int			i;
//
//				rstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalRow;
//				/* Build tupdesc to describe result tuples */
//				if (rowexpr->row_typeid == RECORDOID)
//				{
//					/* generic record, use types of given expressions */
//					rstate->tupdesc = ExecTypeFromExprList(rowexpr->args);
//				}
//				else
//				{
//					/* it's been cast to a named type, use that */
//					rstate->tupdesc = lookup_rowtype_tupdesc_copy(rowexpr->row_typeid, -1);
//				}
//				/* In either case, adopt RowExpr's column aliases */
//				ExecTypeSetColNames(rstate->tupdesc, rowexpr->colnames);
//				/* Bless the tupdesc in case it's now of type RECORD */
//				BlessTupleDesc(rstate->tupdesc);
//				/* Set up evaluation, skipping any deleted columns */
//				Assert(list_length(rowexpr->args) <= rstate->tupdesc->natts);
//				attrs = rstate->tupdesc->attrs;
//				i = 0;
//				foreach(l, rowexpr->args)
//				{
//					Expr	   *e = (Expr *) lfirst(l);
//					ExprState  *estate;
//
//					if (!attrs[i]->attisdropped)
//					{
//						/*
//						 * Guard against ALTER COLUMN TYPE on rowtype since
//						 * the RowExpr was created.  XX should we check
//						 * typmod too?	Not sure we can be sure it'll be the
//						 * same.
//						 */
//						if (exprType((Node *) e) != attrs[i]->atttypid)
//							ereport(ERROR,
//									(errcode(ERRCODE_DATATYPE_MISMATCH),
//									 errmsg("ROW() column has type %s instead of type %s",
//										format_type_be(exprType((Node *) e)),
//									   format_type_be(attrs[i]->atttypid))));
//					}
//					else
//					{
//						/*
//						 * Ignore original expression and insert a NULL. We
//						 * don't really care what type of NULL it is, so
//						 * always make an int4 NULL.
//						 */
//						e = (Expr *) makeNullConst(INT4OID, -1, InvalidOid);
//					}
//					estate = ExecInitExpr(e, parent);
//					outlist = lappend(outlist, estate);
//					i++;
//				}
//				rstate->args = outlist;
//				state = (ExprState *) rstate;
//			}
			break;
		case T_RowCompareExpr:
			PrintLogs("T_RowCompareExpr\t");
//			{
//				RowCompareExpr *rcexpr = (RowCompareExpr *) node;
//				RowCompareExprState *rstate = makeNode(RowCompareExprState);
//				int			nopers = list_length(rcexpr->opnos);
//				List	   *outlist;
//				ListCell   *l;
//				ListCell   *l2;
//				ListCell   *l3;
//				int			i;
//
//				rstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalRowCompare;
//				Assert(list_length(rcexpr->largs) == nopers);
//				outlist = NIL;
//				foreach(l, rcexpr->largs)
//				{
//					Expr	   *e = (Expr *) lfirst(l);
//					ExprState  *estate;
//
//					estate = ExecInitExpr(e, parent);
//					outlist = lappend(outlist, estate);
//				}
//				rstate->largs = outlist;
//				Assert(list_length(rcexpr->rargs) == nopers);
//				outlist = NIL;
//				foreach(l, rcexpr->rargs)
//				{
//					Expr	   *e = (Expr *) lfirst(l);
//					ExprState  *estate;
//
//					estate = ExecInitExpr(e, parent);
//					outlist = lappend(outlist, estate);
//				}
//				rstate->rargs = outlist;
//				Assert(list_length(rcexpr->opfamilies) == nopers);
//				rstate->funcs = (FmgrInfo *) palloc(nopers * sizeof(FmgrInfo));
//				rstate->collations = (Oid *) palloc(nopers * sizeof(Oid));
//				i = 0;
//				forthree(l, rcexpr->opnos, l2, rcexpr->opfamilies, l3, rcexpr->inputcollids)
//				{
//					Oid			opno = lfirst_oid(l);
//					Oid			opfamily = lfirst_oid(l2);
//					Oid			inputcollid = lfirst_oid(l3);
//					int			strategy;
//					Oid			lefttype;
//					Oid			righttype;
//					Oid			proc;
//
//					get_op_opfamily_properties(opno, opfamily, false,
//											   &strategy,
//											   &lefttype,
//											   &righttype);
//					proc = get_opfamily_proc(opfamily,
//											 lefttype,
//											 righttype,
//											 BTORDER_PROC);
//
//					/*
//					 * If we enforced permissions checks on index support
//					 * functions, we'd need to make a check here.  But the
//					 * index support machinery doesn't do that, and neither
//					 * does this code.
//					 */
//					fmgr_info(proc, &(rstate->funcs[i]));
//					rstate->collations[i] = inputcollid;
//					i++;
//				}
//				state = (ExprState *) rstate;
//			}
			break;
		case T_CoalesceExpr:
			PrintLogs("T_CoalesceExpr\t");
//			{
//				CoalesceExpr *coalesceexpr = (CoalesceExpr *) node;
//				CoalesceExprState *cstate = makeNode(CoalesceExprState);
//				List	   *outlist = NIL;
//				ListCell   *l;
//
//				cstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalCoalesce;
//				foreach(l, coalesceexpr->args)
//				{
//					Expr	   *e = (Expr *) lfirst(l);
//					ExprState  *estate;
//
//					estate = ExecInitExpr(e, parent);
//					outlist = lappend(outlist, estate);
//				}
//				cstate->args = outlist;
//				state = (ExprState *) cstate;
//			}
			break;
		case T_MinMaxExpr:
			PrintLogs("T_MinMaxExpr\t");
//			{
//				MinMaxExpr *minmaxexpr = (MinMaxExpr *) node;
//				MinMaxExprState *mstate = makeNode(MinMaxExprState);
//				List	   *outlist = NIL;
//				ListCell   *l;
//				TypeCacheEntry *typentry;
//
//				mstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalMinMax;
//				foreach(l, minmaxexpr->args)
//				{
//					Expr	   *e = (Expr *) lfirst(l);
//					ExprState  *estate;
//
//					estate = ExecInitExpr(e, parent);
//					outlist = lappend(outlist, estate);
//				}
//				mstate->args = outlist;
//				/* Look up the btree comparison function for the datatype */
//				typentry = lookup_type_cache(minmaxexpr->minmaxtype,
//											 TYPECACHE_CMP_PROC);
//				if (!OidIsValid(typentry->cmp_proc))
//					ereport(ERROR,
//							(errcode(ERRCODE_UNDEFINED_FUNCTION),
//							 errmsg("could not identify a comparison function for type %s",
//									format_type_be(minmaxexpr->minmaxtype))));
//
//				/*
//				 * If we enforced permissions checks on index support
//				 * functions, we'd need to make a check here.  But the index
//				 * support machinery doesn't do that, and neither does this
//				 * code.
//				 */
//				fmgr_info(typentry->cmp_proc, &(mstate->cfunc));
//				state = (ExprState *) mstate;
//			}
			break;
		case T_XmlExpr:
			PrintLogs("T_XmlExpr\t");
//			{
//				XmlExpr    *xexpr = (XmlExpr *) node;
//				XmlExprState *xstate = makeNode(XmlExprState);
//				List	   *outlist;
//				ListCell   *arg;
//
//				xstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalXml;
//				outlist = NIL;
//				foreach(arg, xexpr->named_args)
//				{
//					Expr	   *e = (Expr *) lfirst(arg);
//					ExprState  *estate;
//
//					estate = ExecInitExpr(e, parent);
//					outlist = lappend(outlist, estate);
//				}
//				xstate->named_args = outlist;
//
//				outlist = NIL;
//				foreach(arg, xexpr->args)
//				{
//					Expr	   *e = (Expr *) lfirst(arg);
//					ExprState  *estate;
//
//					estate = ExecInitExpr(e, parent);
//					outlist = lappend(outlist, estate);
//				}
//				xstate->args = outlist;
//
//				state = (ExprState *) xstate;
//			}
			break;
		case T_NullTest:
			PrintLogs("T_NullTest\t");
//			{
//				NullTest   *ntest = (NullTest *) node;
//				NullTestState *nstate = makeNode(NullTestState);
//
//				nstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalNullTest;
//				nstate->arg = ExecInitExpr(ntest->arg, parent);
//				nstate->argdesc = NULL;
//				state = (ExprState *) nstate;
//			}
			break;
		case T_BooleanTest:
			PrintLogs("T_BooleanTest\t");
//			{
//				BooleanTest *btest = (BooleanTest *) node;
//				GenericExprState *gstate = makeNode(GenericExprState);
//
//				gstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalBooleanTest;
//				gstate->arg = ExecInitExpr(btest->arg, parent);
//				state = (ExprState *) gstate;
//			}
			break;
		case T_CoerceToDomain:
			PrintLogs("T_CoerceToDomain\t");
//			{
//				CoerceToDomain *ctest = (CoerceToDomain *) node;
//				CoerceToDomainState *cstate = makeNode(CoerceToDomainState);
//
//				cstate->xprstate.evalfunc = (ExprStateEvalFunc) ExecEvalCoerceToDomain;
//				cstate->arg = ExecInitExpr(ctest->arg, parent);
//				cstate->constraints = GetDomainConstraints(ctest->resulttype);
//				state = (ExprState *) cstate;
//			}
			break;
		case T_CurrentOfExpr:
			PrintLogs("T_CurrentOfExpr\t");
//			state = (ExprState *) makeNode(ExprState);
//			state->evalfunc = ExecEvalCurrentOfExpr;
			break;
		case T_TargetEntry:
			{
				TargetEntry *tle = (TargetEntry *) node;
				PrintPlan(tle->expr, parent, estate);
			}
			break;
		case T_List:
			{
				ListCell   *l;

				foreach(l, (List *) node)
				{
					PrintPlan((Expr *) lfirst(l), parent, estate);
				}
				break;
			}
		default:
			// elog(ERROR, "unrecognized node type: %d",
			break;
	}
}
