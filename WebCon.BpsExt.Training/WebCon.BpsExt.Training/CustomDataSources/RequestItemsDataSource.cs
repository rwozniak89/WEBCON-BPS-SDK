using System;
using System.Data;
using System.Linq;
using System.Collections.Generic;
using WebCon.WorkFlow.SDK.DataSourcePlugins;
using WebCon.WorkFlow.SDK.DataSourcePlugins.Model;
using WebCon.WorkFlow.SDK.Common.Model;
using WebCon.WorkFlow.SDK.Tools.Data;
using WebCon.WorkFlow.SDK.Tools.Data.Model;

namespace WebCon.BpsExt.Training.CustomDataSources
{
    public class RequestItemsDataSource : CustomDataSource<RequestItemsDataSourceConfig>
    {
        public override DataTable GetData(SearchConditions searchConditions)
        {
            var result = GenerateDataTable();
            Dictionary<string, string> categoryPersons = GetPersons();

            var items = GetItems();

            foreach (DataRow item in items.Rows)
            {
                var newRow = FillNewRow(result.NewRow(), item, categoryPersons);
                result.Rows.Add(newRow);
            }

            return result;
        }

        private DataTable GenerateDataTable()
        {
            var dt = new DataTable("data");
            foreach (var column in GetColumns())
            {
                dt.Columns.Add(new System.Data.DataColumn(column.Name));
            }

            return dt;
        }

        private Dictionary<string, string> GetPersons()
        {
            var getdataParams = new GetDataTableFromDataSourceParams(Configuration.PersonsDataSourceID, null, Context);
            return DataSourcesHelper.GetDataTableFromDataSource(getdataParams).AsEnumerable()
                .ToDictionary(row => row[Configuration.CategoryColumnName].ToString(),
                row => row[Configuration.PersonColumnName].ToString(), StringComparer.CurrentCultureIgnoreCase);
        }

        private DataTable GetItems()
        {
            var getdataParams = new GetDataTableFromDataSourceParams(Configuration.ResourcesDataSourceID, null, Context);
            return DataSourcesHelper.GetDataTableFromDataSource(getdataParams);
        }

        DataRow FillNewRow(DataRow rowToFill, DataRow item, Dictionary<string, string> categoryPersons)
        {
            rowToFill["ID"] = item["id"];
            rowToFill["Item"] = item["item"];

            var category = item["category"].ToString();
            rowToFill["Category"] = category;

            if (categoryPersons.ContainsKey(category))
                rowToFill["Person"] = categoryPersons[category];

            return rowToFill;
        }

        public override List<DataSourceColumn> GetColumns()
        {
            return new List<DataSourceColumn>()
            {
                new DataSourceColumn("Category","Category"),
                new DataSourceColumn("Item","Item"),
                new DataSourceColumn("ID","ID"),
                new DataSourceColumn("Person","Person")
            };
        }
    }
}