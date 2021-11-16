using System;
using WebCon.WorkFlow.SDK.ActionPlugins;
using WebCon.WorkFlow.SDK.ActionPlugins.Model;
using WebCon.WorkFlow.SDK.Documents;
using WebCon.WorkFlow.SDK.Documents.Model;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class StartNewWorkflowAction : CustomAction<StartNewWorkflowActionConfig>
    {
        public override void Run(RunCustomActionParams args)
        {
            var newDocument = DocumentsManager.GetNewDocument(new GetNewDocumentParams(Configuration.DoctypeID, Configuration.WorkflowID));
            DocumentsManager.StartNewWorkFlow(new StartNewWorkFlowParams(newDocument, Configuration.StartingPathID));
        }
    }
}