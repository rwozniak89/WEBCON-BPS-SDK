using WebCon.WorkFlow.SDK.Common;
using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.CustomDataSources
{
    public class RequestItemsDataSourceConfig : PluginConfiguration
    {
        [ConfigEditableDataSourceID(DisplayName = "Responsible persons", Description = "Datasource of persons responsible for resource categories", IsRequired = true)]
        public int PersonsDataSourceID { get; set; }

        [ConfigEditableText(DisplayName = "Column of the person", Description = "Name of the column with the person responsible for resource categories", IsRequired = true)]
        public string PersonColumnName { get; set; }

        [ConfigEditableText(DisplayName = "Column of the category", Description = "Name of the column with the resource category", IsRequired = true)]
        public string CategoryColumnName { get; set; }

        [ConfigEditableDataSourceID(DisplayName = "Resources", SourcesType = DataSourceType.WebServiceREST, Description = "Resources datasource", IsRequired = true)]
        public int ResourcesDataSourceID { get; set; }
    }
}