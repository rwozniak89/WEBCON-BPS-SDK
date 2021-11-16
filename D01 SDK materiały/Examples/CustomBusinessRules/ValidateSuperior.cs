using System.Data;
using System.Linq;
using WebCon.WorkFlow.SDK.BusinessRulePlugins;
using WebCon.WorkFlow.SDK.BusinessRulePlugins.Model;
using WebCon.WorkFlow.SDK.Common.Model;
using WebCon.WorkFlow.SDK.Tools.Data.Model;
using System;
using WebCon.WorkFlow.SDK.Tools.Other;
using WebCon.WorkFlow.SDK.Tools.Data;

namespace WebCon.BpsExt.Training.CustomBusinessRules
{
    public class ValidateSuperior : CustomBusinessRule<ValidateSuperiorConfig>
    {
        public override EvaluationResult Evaluate(CustomBusinessRuleParams args)
        {
            bool isAcceptor = !string.IsNullOrEmpty(Configuration.CurrentSuperior) && CanAcceptRequest(TextHelper.GetPairId(Configuration.CurrentSuperior),args.Context);
            return EvaluationResult.CreateBoolResult(isAcceptor);
        }

        bool CanAcceptRequest(string currentSupperiorID, ProcessContext context)
        {
            var getParams = new GetDataTableFromDataSourceParams(Configuration.SuperiorsDataSourceID, null, context);
            var superiorsDT = DataSourcesHelper.GetDataTableFromDataSource(getParams);
            return superiorsDT.AsEnumerable().Any(superior => superior["ID"].ToString().Equals(currentSupperiorID, StringComparison.CurrentCultureIgnoreCase));
        }
    }
}