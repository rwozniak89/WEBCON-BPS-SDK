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
    }
}