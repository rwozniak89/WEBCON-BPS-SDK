using Newtonsoft.Json;
using System;
using System.Net.Http;
using System.Text;
using WebCon.WorkFlow.SDK.ActionPlugins;
using WebCon.WorkFlow.SDK.ActionPlugins.Model;
using WebCon.WorkFlow.SDK.Tools.Other;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class RegisterWorkerRequest : CustomAction<RegisterWorkerRequestConfig>
    {
        public override void Run(RunCustomActionParams args)
        {
            var requestData = new RequestData(TextHelper.GetPairId(Configuration.Person), Configuration.Amount);
            var requestInfo = RegisterRequest(requestData);
            args.Context.CurrentDocument.SetFieldValue(Configuration.FieldRequestID, requestInfo.requestId);

            args.TransitionInfo.TasksToAdd.Add(requestInfo.managerId, null);
        }

        private RequestInfo RegisterRequest(RequestData requestData)
        {
            return CallERPService<RequestInfo>(Configuration.WebServiceUrl, requestData);
        }

        private T CallERPService<T>(string url, RequestData data)
        {
            string jsonRequest = JsonConvert.SerializeObject(data);
            var content = new StringContent(jsonRequest, Encoding.UTF8, "application/json");

            var client = new HttpClient();
            var response = client.PostAsync(url, content).Result;
            response.EnsureSuccessStatusCode();
            var result = response.Content.ReadAsStringAsync().Result;
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

        public class RequestInfo
        {
            public string managerId { get; set; }
            public int requestId { get; set; }
        }
    }
}