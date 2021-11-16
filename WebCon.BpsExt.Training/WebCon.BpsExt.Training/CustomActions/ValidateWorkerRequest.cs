using System;
using WebCon.WorkFlow.SDK.ActionPlugins;
using WebCon.WorkFlow.SDK.ActionPlugins.Model;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class ValidateWorkerRequest : CustomAction<ValidateWorkerRequestConfig>
    {
        public override void Run(RunCustomActionParams args)
        {
            //RunWithoutDocumentContext(new RunCustomActionWithoutContextParams(args));

            //Copy value from source form field to destination form field
            //string sourceFormFieldValue = args.Context.CurrentDocument.GetFieldValue(Configuration.SourceFormFieldID).ToString();
            //args.Context.CurrentDocument.SetFieldValue(Configuration.DestinationFormFieldID, sourceFormFieldValue);

            //Save value to form field
            //args.Context.CurrentDocument.SetFieldValue(Configuration.PriceFormFieldID, Configuration.Price);
        }

        public override void RunWithoutDocumentContext(RunCustomActionWithoutContextParams args)
        {
            base.RunWithoutDocumentContext(args);
        }
    }
}