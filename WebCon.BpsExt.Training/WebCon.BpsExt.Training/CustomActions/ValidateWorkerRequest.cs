using Newtonsoft.Json;
using System;
using System.Net.Http;
using System.Text;
using System.Threading.Tasks;
using WebCon.WorkFlow.SDK.ActionPlugins;
using WebCon.WorkFlow.SDK.ActionPlugins.Model;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class ValidateWorkerRequest : CustomAction<ValidateWorkerRequestConfig>
    {
        private StringBuilder _log = new StringBuilder();
        public override void Run(RunCustomActionParams args)
        {
            try
            {
                if (!IsRequestValid(new RequestData(Configuration.Person, Configuration.Amount)))
                {
                    args.HasErrors = true;
                    args.Message = string.Format(Configuration.ValidationMessages.InvalidRequestMessage, Configuration.Amount);
                        //string.Format("You can't request an amount of {0}", Configuration.Amount);
                }
            }
            catch (Exception ex)
            {
                args.HasErrors = true;
                args.Message = ex.Message;
                _log.AppendLine(ex.ToString());
            }
            finally
            {
                var log = _log.ToString();
                args.Context.PluginLogger.AppendDebug(log);
                args.LogMessage = log;
            }
                      
           
        }

        private bool IsRequestValid(RequestData requestData)
        {
            return CallERPService<bool>(Configuration.WebServiceUrl, requestData).Result;
        }

        private async Task<T> CallERPService<T>(string url, RequestData data)
        {
            string jsonRequest = JsonConvert.SerializeObject(data);
            var content = new StringContent(jsonRequest, Encoding.UTF8, "application/json");

            var client = new HttpClient();
            var response = await client.PostAsync(url, content);
            response.EnsureSuccessStatusCode();
            var result = await response.Content.ReadAsStringAsync();
            T jsonResult = JsonConvert.DeserializeObject<T>(result);
            return jsonResult;
        }

        public class RequestData
        {
            public string bpsId { get; set; }
            public decimal amount { get; set; }

            public RequestData(string bpsId, decimal amount)
            {
                this.bpsId = bpsId;
                this.amount = amount;
            }
        }
    }
}