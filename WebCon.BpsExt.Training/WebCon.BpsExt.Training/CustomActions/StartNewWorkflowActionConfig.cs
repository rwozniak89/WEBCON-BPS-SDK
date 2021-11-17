using System.Collections.Generic;
using WebCon.WorkFlow.SDK.Common;
using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class StartNewWorkflowActionConfig : PluginConfiguration
    {
        [ConfigEditableText(DisplayName = "Form type ID", IsRequired = true)]
        public int DoctypeID { get; set; }

        [ConfigEditableText(DisplayName = "Workflow ID", IsRequired = true)]
        public int WorkflowID { get; set; }

        [ConfigEditableText(DisplayName = "Starting path ID", IsRequired = true)]
        public int StartingPathID { get; set; }

        //https://srv38.webconbps.com/db/1007/app/6/tasks/element/12/form

        [ConfigEditableText("PortalUrl", isRequired: true, DefaultText = ("https://srv38.webconbps.com/"))]
        public string PortalUrl { get; set; }

        [ConfigEditableFormFieldID("Created element id sygnature")]
        public int SygnatureFieldId { get; set; }

        [ConfigEditableGrid(DisplayName = "Fields valuess")]
        public List<FieldValue> FieldValues { get; set; }

        [ConfigEditableText("ParentId", IsRequired = true, Multiline = true, TagEvaluationMode = EvaluationMode.SQL)] //, DefaultText = "{WFD_ID}")]
        public string ParentIdQuery { get; set; }
    }


    public class FieldValue
    {
        [ConfigEditableGridColumn(DisplayName = "Value")]
        public string Value { get; set; }

        [ConfigEditableGridColumnFormFieldID(DisplayName = "Field ID")]
        public int FieldId { get; set; }

    }
}