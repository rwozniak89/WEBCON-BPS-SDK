using System;
using System.Linq;
using WebCon.WorkFlow.SDK.ActionPlugins;
using WebCon.WorkFlow.SDK.ActionPlugins.Model;
using WebCon.WorkFlow.SDK.Documents;
using WebCon.WorkFlow.SDK.Documents.Model;
using WebCon.WorkFlow.SDK.Documents.Model.Attachments;
using WebCon.WorkFlow.SDK.Tools.Data;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class StartNewWorkflowAction : CustomAction<StartNewWorkflowActionConfig>
    {
        public override void Run(RunCustomActionParams args)
        {
            var elementId = GenetrateNewDocument(args.Context.CurrentDocument);
            var url = $"{Configuration.PortalUrl}/db/1007/app/6/tasks/element/{elementId}/form";

            //if (args.TransitionInfo != null)
            //    args.TransitionInfo.RedirectUrl(url);
            //else
            //    base.CustomJavascript = $"alert(\"Test\"); window.open('{url}')";

        }


        private int GenetrateNewDocument(ExistingDocumentData parentDocument)
        {
            var newDocument = DocumentsManager.GetNewDocument(new GetNewDocumentParams(Configuration.DoctypeID, Configuration.WorkflowID)
            { SkipPermissionsCheck = true , ParentDocumentID = parentDocument.ID});

            //newDocument.SetFieldValue(Configuration.FieldId, "")

            foreach (var filed in Configuration.FieldValues)
                newDocument.SetFieldValue(filed.FieldId, filed.Value);

            //if(parentDocument.Attachments.Any())
            //{
            //    var att = parentDocument.Attachments.First();
            //    //new NewAttachmentData() { }
            //    newDocument.Attachments.AddNew(att);
            //}


            var result = DocumentsManager.StartNewWorkFlow(new StartNewWorkFlowParams(newDocument, Configuration.StartingPathID)
            { SkipPermissionsCheck = true });

            parentDocument.SetFieldValue(Configuration.SygnatureFieldId, result.CreatedDocumentID);

            return result.CreatedDocumentID;
        }

        public override void RunWithoutDocumentContext(RunCustomActionWithoutContextParams args)
        {
            using (var transactionScope = new BPSTransactionScope(args.Context))
            {
                var parentDocumen = GetParent();

                //DocumentAttachmentsManager.GetAttachments(new GetAttachmentsParams() { DocumentId = parentDocumen.ID });

                GenetrateNewDocument(parentDocumen);

                DocumentsManager.UpdateDocument(new UpdateDocumentParams(parentDocumen) { ForceCheckout = true, SkipPermissionsCheck = true });

                transactionScope.Complete();
            }


               
        }

        private ExistingDocumentData GetParent()
        {
            var parentId = (int)SqlExecutionHelper.ExecSqlCommandScalarOutsideTransaction(Configuration.ParentIdQuery);
            return DocumentsManager.GetDocumentByID(parentId, true);
        }
    }
}