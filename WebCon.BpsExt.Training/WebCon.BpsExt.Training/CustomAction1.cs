using System;
using WebCon.WorkFlow.SDK.ActionPlugins;
using WebCon.WorkFlow.SDK.ActionPlugins.Model;

namespace WebCon.BpsExt.Training
{
    public class CustomAction1 : CustomAction<CustomAction1Config>
    {
        public override void Run(RunCustomActionParams args)
        {
            //Copy value from source form field to destination form field
            //string sourceFormFieldValue = args.Context.CurrentDocument.GetFieldValue(Configuration.SourceFormFieldID).ToString();
            //args.Context.CurrentDocument.SetFieldValue(Configuration.DestinationFormFieldID, sourceFormFieldValue);

            //Save value to form field
            //args.Context.CurrentDocument.SetFieldValue(Configuration.PriceFormFieldID, Configuration.Price);
        }
    }
}