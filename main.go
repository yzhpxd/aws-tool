package main

import (
	"archive/zip"
	"bufio"
	"bytes"
	"context"
	"encoding/base64"
	"errors"
	"fmt"
	"math/rand"
	"net/http"
	"net/url"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"
	"text/tabwriter"
	"time"

	"github.com/aws/aws-sdk-go-v2/aws"
	"github.com/aws/aws-sdk-go-v2/config"
	"github.com/aws/aws-sdk-go-v2/credentials"
	"github.com/aws/aws-sdk-go-v2/service/account"
	"github.com/aws/aws-sdk-go-v2/service/budgets"
	budgetsTypes "github.com/aws/aws-sdk-go-v2/service/budgets/types"
	"github.com/aws/aws-sdk-go-v2/service/ec2"
	ec2t "github.com/aws/aws-sdk-go-v2/service/ec2/types"
	"github.com/aws/aws-sdk-go-v2/service/iam"
	"github.com/aws/aws-sdk-go-v2/service/lambda"
	lambdaTypes "github.com/aws/aws-sdk-go-v2/service/lambda/types"
	"github.com/aws/aws-sdk-go-v2/service/lightsail"
	lst "github.com/aws/aws-sdk-go-v2/service/lightsail/types"
	"github.com/aws/aws-sdk-go-v2/service/rds"
	"github.com/aws/aws-sdk-go-v2/service/servicequotas"
	"github.com/aws/aws-sdk-go-v2/service/sts"
)

/*
AWS Manager (Go) - 全能网络版 (自动修复 + 支持新区域自动开通)
- IPv6: 遇错直接修复，不询问
- IPv4: 支持弹性 IP 管理
*/

const bootstrapRegion = "us-east-1"

var GlobalProxy string

// --- 数据结构 ---

type LSInstanceRow struct {
	Idx    int
	Region string
	Name   string
	State  string
	IP     string
	IPv6   string
	AZ     string
	Bundle string
}

type EC2InstanceRow struct {
	Idx    int
	Region string
	AZ     string
	ID     string
	State  string
	Name   string
	Type   string
	PubIP  string
	PrivIP string
	IPv6   string
}

type RegionInfo struct {
	Name   string
	Status string
}

type AMIOption struct {
	Name    string
	Owner   string
	Pattern string
}

type TypeOption struct {
	Type string
	Desc string
}

// -------------------- UI/辅助函数 --------------------

func parseProxyString(raw string) string {
	raw = strings.TrimSpace(raw)
	if raw == "" {
		return ""
	}
	if strings.Contains(raw, "://") {
		return raw
	}
	parts := strings.Split(raw, ":")
	if len(parts) == 2 {
		return fmt.Sprintf("socks5://%s:%s", parts[0], parts[1])
	}
	if len(parts) == 4 {
		userInfo := url.UserPassword(parts[2], parts[3]).String()
		return fmt.Sprintf("socks5://%s@%s:%s", userInfo, parts[0], parts[1])
	}
	return raw
}

func regionCN(region string) string {
	m := map[string]string{
		"af-south-1": "南非·开普敦", "ap-east-1": "中国·香港", "ap-east-2": "中国·台湾",
		"ap-northeast-1": "日本·东京", "ap-northeast-2": "韩国·首尔", "ap-northeast-3": "日本·大阪",
		"ap-south-1": "印度·孟买", "ap-south-2": "印度·海得拉巴", "ap-southeast-1": "新加坡",
		"ap-southeast-2": "澳大利亚·悉尼", "ap-southeast-3": "印度尼西亚·雅加达", "ap-southeast-4": "澳大利亚·墨尔本",
		"ap-southeast-5": "马来西亚·吉隆坡", "ap-southeast-6": "亚太·其他", "ap-southeast-7": "泰国·曼谷",
		"ca-central-1": "加拿大·中部", "ca-west-1": "加拿大·卡尔加里", "eu-central-1": "德国·法兰克福",
		"eu-central-2": "瑞士·苏黎世", "eu-north-1": "瑞典·斯德哥尔摩", "eu-south-1": "意大利·米兰",
		"eu-south-2": "西班牙·马德里", "eu-west-1": "爱尔兰·都柏林", "eu-west-2": "英国·伦敦",
		"eu-west-3": "法国·巴黎", "il-central-1": "以色列·特拉维夫", "me-central-1": "阿联酋·阿布扎比",
		"me-south-1": "巴林", "mx-central-1": "墨西哥·中心", "sa-east-1": "巴西·圣保罗",
		"us-east-1": "美国东部·弗吉尼亚", "us-east-2": "美国东部·俄亥俄", "us-west-1": "美国西部·加州(北)",
		"us-west-2": "美国西部·俄勒冈",
	}
	if v, ok := m[region]; ok {
		return v
	}
	return "未知区域"
}

func input(prompt, def string) string {
	fmt.Print(prompt)
	r := bufio.NewReader(os.Stdin)
	s, _ := r.ReadString('\n')
	s = strings.TrimSpace(s)
	if s == "" {
		return def
	}
	return s
}

func inputSecret(prompt string) string {
	fmt.Print(prompt)
	r := bufio.NewReader(os.Stdin)
	s, _ := r.ReadString('\n')
	return strings.TrimSpace(s)
}

func mustInt(s string) int {
	i, err := strconv.Atoi(strings.TrimSpace(s))
	if err != nil {
		return -1
	}
	return i
}

func cut(s string, n int) string {
	if n <= 0 {
		return ""
	}
	if len(s) <= n {
		return s
	}
	return s[:n]
}

func yes(s string) bool {
	s = strings.TrimSpace(strings.ToLower(s))
	return s == "y" || s == "yes"
}

func randStr(n int) string {
	const letters = "abcdefghijklmnopqrstuvwxyz0123456789"
	b := make([]byte, n)
	for i := range b {
		b[i] = letters[rand.Intn(len(letters))]
	}
	return string(b)
}

func collectUserData(promptTitle string) (raw string, isEmpty bool) {
	fmt.Println(promptTitle)
	fmt.Println("（直接回车跳过；如需输入多行，请输入内容后另起一行输入 END 结束）")
	var lines []string
	for {
		l := input("> ", "")
		if l == "" && len(lines) == 0 {
			return "", true
		}
		if l == "END" {
			break
		}
		lines = append(lines, l)
	}
	return strings.Join(lines, "\n"), len(lines) == 0
}

func mkCfg(ctx context.Context, region string, creds aws.CredentialsProvider) (aws.Config, error) {
	opts := []func(*config.LoadOptions) error{
		config.WithRegion(region),
		config.WithCredentialsProvider(creds),
	}
	if GlobalProxy != "" {
		proxyURL, err := url.Parse(GlobalProxy)
		if err == nil {
			httpClient := &http.Client{
				Transport: &http.Transport{Proxy: http.ProxyURL(proxyURL)},
				Timeout:   30 * time.Second,
			}
			opts = append(opts, config.WithHTTPClient(httpClient))
		}
	}
	return config.LoadDefaultConfig(ctx, opts...)
}

func stsCheck(ctx context.Context, region string, creds aws.CredentialsProvider) error {
	cfg, err := mkCfg(ctx, region, creds)
	if err != nil {
		return err
	}
	cli := sts.NewFromConfig(cfg)
	_, err = cli.GetCallerIdentity(ctx, &sts.GetCallerIdentityInput{})
	return err
}

func pickRegion(title string, items []RegionInfo, def string) (RegionInfo, error) {
	if len(items) == 0 {
		return RegionInfo{}, errors.New("列表为空")
	}
	fmt.Println(title)
	defIdx := 1
	for i := range items {
		if items[i].Name == def {
			defIdx = i + 1
			break
		}
	}
	for i, it := range items {
		statusMark := ""
		if it.Status == "not-opted-in" {
			statusMark = " [⚠️ 未启用]"
		} else if it.Status == "opted-in" {
			statusMark = " [已启用]"
		}
		fmt.Printf("  %2d) %-14s --- %s%s\n", i+1, it.Name, regionCN(it.Name), statusMark)
	}
	s := input(fmt.Sprintf("请输入编号 [%d]: ", defIdx), fmt.Sprintf("%d", defIdx))
	idx := mustInt(s)
	if idx < 1 || idx > len(items) {
		return RegionInfo{}, fmt.Errorf("编号无效")
	}
	return items[idx-1], nil
}

func pickFromList(title string, items []string, def string) (string, error) {
	if len(items) == 0 {
		return "", errors.New("列表为空")
	}
	fmt.Println(title)
	defIdx := 1
	for i := range items {
		if items[i] == def {
			defIdx = i + 1
			break
		}
	}
	for i, it := range items {
		fmt.Printf("  %2d) %-14s ------- %s\n", i+1, it, regionCN(it))
	}
	s := input(fmt.Sprintf("请输入编号 [%d]: ", defIdx), fmt.Sprintf("%d", defIdx))
	idx := mustInt(s)
	if idx < 1 || idx > len(items) {
		return "", fmt.Errorf("编号无效")
	}
	return items[idx-1], nil
}

func printTable(header string, rowsFunc func(*tabwriter.Writer)) {
	w := tabwriter.NewWriter(os.Stdout, 0, 0, 2, ' ', 0)
	fmt.Fprintln(w, header)
	rowsFunc(w)
	w.Flush()
}

// -------------------- 2. 自动化 $80 任务逻辑 --------------------

func taskSetBudget(ctx context.Context, cfg aws.Config, acctID string) {
	fmt.Println("\n[任务 1/4] 正在设置 AWS Cost Budget (成本预算)...")
	cli := budgets.NewFromConfig(cfg)
	budgetName := fmt.Sprintf("AutoBudget-%s", randStr(6))
	email := fmt.Sprintf("alert-%s@gmail.com", randStr(4))
	_, err := cli.CreateBudget(ctx, &budgets.CreateBudgetInput{
		AccountId: aws.String(acctID),
		Budget: &budgetsTypes.Budget{
			BudgetName:  aws.String(budgetName),
			BudgetType:  budgetsTypes.BudgetTypeCost,
			TimeUnit:    budgetsTypes.TimeUnitMonthly,
			BudgetLimit: &budgetsTypes.Spend{Amount: aws.String("10.0"), Unit: aws.String("USD")},
		},
		NotificationsWithSubscribers: []budgetsTypes.NotificationWithSubscribers{
			{
				Notification: &budgetsTypes.Notification{
					NotificationType:   budgetsTypes.NotificationTypeActual,
					ComparisonOperator: budgetsTypes.ComparisonOperatorGreaterThan,
					Threshold:          80.0,
				},
				Subscribers: []budgetsTypes.Subscriber{{SubscriptionType: budgetsTypes.SubscriptionTypeEmail, Address: aws.String(email)}},
			},
		},
	})
	if err != nil {
		if strings.Contains(err.Error(), "Duplicate") {
			fmt.Println(" ✅ 预算已存在，跳过。")
		} else {
			fmt.Printf(" ❌ 失败: %v\n", err)
		}
	} else {
		fmt.Printf(" ✅ 预算 [%s] 创建成功\n", budgetName)
	}
}

func taskRunEC2(ctx context.Context, cfg aws.Config) {
	fmt.Println("\n[任务 2/4] 正在启动 EC2 实例...")
	cli := ec2.NewFromConfig(cfg)
	ami := "ami-051f7e7f6c2f40dc1"
	runOut, err := cli.RunInstances(ctx, &ec2.RunInstancesInput{
		ImageId:      aws.String(ami),
		InstanceType: ec2t.InstanceTypeT3Micro,
		MinCount:     aws.Int32(1),
		MaxCount:     aws.Int32(1),
	})
	if err != nil {
		fmt.Printf(" ❌ 启动失败: %v\n", err)
		return
	}
	id := *runOut.Instances[0].InstanceId
	fmt.Printf(" ⏳ 实例 %s 启动中，等待 Running...\n", id)
	for i := 0; i < 40; i++ {
		time.Sleep(3 * time.Second)
		desc, _ := cli.DescribeInstances(ctx, &ec2.DescribeInstancesInput{InstanceIds: []string{id}})
		if len(desc.Reservations) > 0 && desc.Reservations[0].Instances[0].State.Name == ec2t.InstanceStateNameRunning {
			fmt.Println(" ✅ 状态: Running (任务达成)")
			break
		}
		fmt.Print(".")
	}
	fmt.Println(" 🗑️ 正在终止实例...")
	cli.TerminateInstances(ctx, &ec2.TerminateInstancesInput{InstanceIds: []string{id}})
	fmt.Println(" ✅ 实例已终止")
}

func taskRunLambda(ctx context.Context, cfg aws.Config) {
	fmt.Println("\n[任务 3/4] 正在创建并调用 Lambda 函数...")
	iamCli := iam.NewFromConfig(cfg)
	roleName := fmt.Sprintf("AutoLambdaRole-%s", randStr(5))
	assumeRolePolicy := `{"Version": "2012-10-17","Statement": [{"Effect": "Allow","Principal": {"Service": "lambda.amazonaws.com"},"Action": "sts:AssumeRole"}]}`
	fmt.Printf(" -> 创建临时 IAM 角色: %s\n", roleName)
	roleOut, err := iamCli.CreateRole(ctx, &iam.CreateRoleInput{
		RoleName:                 aws.String(roleName),
		AssumeRolePolicyDocument: aws.String(assumeRolePolicy),
	})
	if err != nil {
		fmt.Printf(" ❌ IAM 角色创建失败: %v\n", err)
		return
	}
	roleArn := *roleOut.Role.Arn
	fmt.Print(" ⏳ 等待 IAM 角色生效 (约10秒)...")
	time.Sleep(10 * time.Second)
	fmt.Println("")

	code := `def lambda_handler(event, context): return "Hello AWS 80 USD"`
	buf := new(bytes.Buffer)
	zipWriter := zip.NewWriter(buf)
	f, _ := zipWriter.Create("lambda_function.py")
	f.Write([]byte(code))
	zipWriter.Close()

	lambdaCli := lambda.NewFromConfig(cfg)
	funcName := fmt.Sprintf("AutoFunc-%s", randStr(5))
	_, err = lambdaCli.CreateFunction(ctx, &lambda.CreateFunctionInput{
		FunctionName: aws.String(funcName),
		Runtime:      lambdaTypes.RuntimePython39,
		Role:         aws.String(roleArn),
		Handler:      aws.String("lambda_function.lambda_handler"),
		Code:         &lambdaTypes.FunctionCode{ZipFile: buf.Bytes()},
	})
	if err != nil {
		time.Sleep(5 * time.Second)
		_, err = lambdaCli.CreateFunction(ctx, &lambda.CreateFunctionInput{
			FunctionName: aws.String(funcName),
			Runtime:      lambdaTypes.RuntimePython39,
			Role:         aws.String(roleArn),
			Handler:      aws.String("lambda_function.lambda_handler"),
			Code:         &lambdaTypes.FunctionCode{ZipFile: buf.Bytes()},
		})
		if err != nil {
			fmt.Printf(" ❌ 函数创建失败: %v\n", err)
			iamCli.DeleteRole(ctx, &iam.DeleteRoleInput{RoleName: aws.String(roleName)})
			return
		}
	}
	fmt.Printf(" ✅ 函数 %s 创建成功，正在初始化...\n", funcName)
	fmt.Print(" ⏳ 等待函数就绪 (Pending -> Active)")
	for i := 0; i < 30; i++ {
		fOut, err := lambdaCli.GetFunction(ctx, &lambda.GetFunctionInput{FunctionName: aws.String(funcName)})
		if err == nil && fOut.Configuration.State == lambdaTypes.StateActive {
			fmt.Println(" ✅ 就绪")
			break
		}
		time.Sleep(2 * time.Second)
		fmt.Print(".")
	}
	_, err = lambdaCli.Invoke(ctx, &lambda.InvokeInput{FunctionName: aws.String(funcName)})
	if err == nil {
		fmt.Println(" ✅ 调用成功！任务达成。")
	} else {
		fmt.Printf(" ❌ 调用失败: %v\n", err)
	}
	fmt.Println(" 🗑️ 清理资源...")
	lambdaCli.DeleteFunction(ctx, &lambda.DeleteFunctionInput{FunctionName: aws.String(funcName)})
	iamCli.DeleteRole(ctx, &iam.DeleteRoleInput{RoleName: aws.String(roleName)})
}

func taskRunRDS(ctx context.Context, cfg aws.Config) {
	fmt.Println("\n[任务 4/4] 正在创建 RDS 数据库 (MySQL Free Tier)...")
	fmt.Println("⚠️ 警告：RDS 创建非常慢 (5-10 分钟)，请耐心等待。")
	rdsCli := rds.NewFromConfig(cfg)
	dbName := fmt.Sprintf("db-%s", randStr(6))
	masterUser := "admin"
	masterPass := "Password123456"
	_, err := rdsCli.CreateDBInstance(ctx, &rds.CreateDBInstanceInput{
		DBInstanceIdentifier:  aws.String(dbName),
		DBInstanceClass:       aws.String("db.t3.micro"),
		Engine:                aws.String("mysql"),
		MasterUsername:        aws.String(masterUser),
		MasterUserPassword:    aws.String(masterPass),
		AllocatedStorage:      aws.Int32(20),
		BackupRetentionPeriod: aws.Int32(0),
	})
	if err != nil {
		fmt.Printf(" ❌ 创建请求失败: %v\n", err)
		return
	}
	fmt.Printf(" ⏳ 数据库 %s 正在创建...\n", dbName)
	ticker := time.NewTicker(30 * time.Second)
	defer ticker.Stop()
	maxWait := 30
	created := false
	for i := 0; i < maxWait; i++ {
		<-ticker.C
		out, err := rdsCli.DescribeDBInstances(ctx, &rds.DescribeDBInstancesInput{
			DBInstanceIdentifier: aws.String(dbName),
		})
		if err != nil {
			fmt.Print("x")
			continue
		}
		if len(out.DBInstances) > 0 {
			status := aws.ToString(out.DBInstances[0].DBInstanceStatus)
			fmt.Printf("[%s] ", status)
			if status == "available" {
				created = true
				fmt.Println("\n ✅ 数据库已就绪！任务达成。")
				break
			}
		}
	}
	if created {
		fmt.Println(" 🗑️ 正在删除数据库...")
		_, err := rdsCli.DeleteDBInstance(ctx, &rds.DeleteDBInstanceInput{
			DBInstanceIdentifier: aws.String(dbName),
			SkipFinalSnapshot:    aws.Bool(true),
		})
		if err != nil {
			fmt.Printf(" ❌ 删除失败: %v\n", err)
		} else {
			fmt.Println(" ✅ 删除指令已发送。")
		}
	} else {
		fmt.Println("\n ⚠️ 等待超时，数据库可能仍在创建中。请稍后务必手动删除！")
	}
}

func autoClaimCredits(ctx context.Context, creds aws.CredentialsProvider) {
	fmt.Println("\n====== 💰 自动执行 AWS 新手任务 (赚取 $80 抵扣金) ======")
	fmt.Println("区域：强制使用 us-east-1")
	fmt.Println("\n请选择模式:")
	fmt.Println(" 1) 全自动 (跑完所有 4 个任务)")
	fmt.Println(" 2) 自选任务")
	mode := input("选择 [1]: ", "1")
	cfg, err := mkCfg(ctx, "us-east-1", creds)
	if err != nil {
		fmt.Println("初始化配置失败:", err)
		return
	}
	stsCli := sts.NewFromConfig(cfg)
	idOut, err := stsCli.GetCallerIdentity(ctx, &sts.GetCallerIdentityInput{})
	if err != nil {
		fmt.Println("获取账户 ID 失败:", err)
		return
	}
	acctID := *idOut.Account
	if mode == "1" {
		taskSetBudget(ctx, cfg, acctID)
		taskRunEC2(ctx, cfg)
		taskRunLambda(ctx, cfg)
		taskRunRDS(ctx, cfg)
	} else {
		for {
			fmt.Println("\n--- 任务选择 ---")
			fmt.Println(" 1. 设置预算")
			fmt.Println(" 2. 启动 EC2")
			fmt.Println(" 3. 运行 Lambda")
			fmt.Println(" 4. 创建 RDS")
			fmt.Println(" 0. 返回")
			t := input("请输入任务编号: ", "0")
			if t == "0" {
				break
			}
			switch t {
			case "1":
				taskSetBudget(ctx, cfg, acctID)
			case "2":
				taskRunEC2(ctx, cfg)
			case "3":
				taskRunLambda(ctx, cfg)
			case "4":
				taskRunRDS(ctx, cfg)
			default:
				fmt.Println("无效选项")
			}
		}
	}
	if mode == "1" {
		fmt.Println("\n====== 🎉 所有流程执行完毕 ======")
		input("按回车键返回主菜单...", "")
	}
}

// -------------------- 3. AWS 功能函数 (EC2, Lightsail) --------------------

func getEC2RegionsWithStatus(ctx context.Context, creds aws.CredentialsProvider) ([]RegionInfo, error) {
	cfg, err := mkCfg(ctx, bootstrapRegion, creds)
	if err != nil {
		return nil, err
	}
	cli := ec2.NewFromConfig(cfg)
	out, err := cli.DescribeRegions(ctx, &ec2.DescribeRegionsInput{AllRegions: aws.Bool(true)})
	if err != nil {
		return nil, err
	}
	var rs []RegionInfo
	for _, r := range out.Regions {
		if r.RegionName != nil && *r.RegionName != "" {
			rs = append(rs, RegionInfo{Name: *r.RegionName, Status: aws.ToString(r.OptInStatus)})
		}
	}
	sort.Slice(rs, func(i, j int) bool { return rs[i].Name < rs[j].Name })
	return rs, nil
}

func getLightsailRegions(ctx context.Context, creds aws.CredentialsProvider) ([]string, error) {
	cfg, err := mkCfg(ctx, bootstrapRegion, creds)
	if err != nil {
		return nil, err
	}
	cli := lightsail.NewFromConfig(cfg)
	out, err := cli.GetRegions(ctx, &lightsail.GetRegionsInput{})
	if err != nil {
		return nil, err
	}
	var rs []string
	for _, r := range out.Regions {
		name := string(r.Name)
		if name != "" {
			rs = append(rs, name)
		}
	}
	sort.Strings(rs)
	return rs, nil
}

// 修复点 1：加强区域开通探测，必须等待 IAM 和新区域网络端点同步完成
func ensureRegionOptIn(ctx context.Context, regionName, currentStatus string, creds aws.CredentialsProvider) error {
	if currentStatus == "opt-in-not-required" || currentStatus == "opted-in" {
		return nil
	}
	fmt.Printf("\n⚠️  检测到区域 %s 未启用 (当前状态: %s)\n", regionName, currentStatus)
	if !yes(input("是否发送启用请求并等待？(可能需要5-15分钟) [y/N]: ", "n")) {
		return fmt.Errorf("已取消")
	}

	cfg, err := mkCfg(ctx, bootstrapRegion, creds)
	if err != nil {
		return err
	}
	acctCli := account.NewFromConfig(cfg)

	if currentStatus != "enabling" {
		_, err = acctCli.EnableRegion(ctx, &account.EnableRegionInput{RegionName: aws.String(regionName)})
		if err != nil {
			if !strings.Contains(err.Error(), "ResourceAlreadyExists") && !strings.Contains(err.Error(), "Region is enabled") {
				return fmt.Errorf("启用请求发送失败: %v", err)
			}
		}
		fmt.Println("✅ 启用请求已发送")
	}

	ec2Cli := ec2.NewFromConfig(cfg)
	ticker := time.NewTicker(15 * time.Second)
	defer ticker.Stop()

	fmt.Print("⏳ 等待区域状态变为 opted-in...")
	optedIn := false
	for i := 0; i < 40; i++ { // wait up to 10 mins
		<-ticker.C
		out, err := ec2Cli.DescribeRegions(ctx, &ec2.DescribeRegionsInput{
			RegionNames: []string{regionName},
			AllRegions:  aws.Bool(true),
		})
		if err != nil {
			fmt.Print("x")
			continue
		}
		if len(out.Regions) > 0 {
			status := aws.ToString(out.Regions[0].OptInStatus)
			if status == "opted-in" {
				optedIn = true
				fmt.Println("\n✅ 区域状态已更新为 opted-in！")
				break
			}
		}
		fmt.Print(".")
	}

	if !optedIn {
		return fmt.Errorf("等待超时，区域仍在开通中，请稍后重新运行脚本。")
	}

	fmt.Print("⏳ 等待新区域的 API 权限完全同步 (IAM)...")
	targetCfg, _ := mkCfg(ctx, regionName, creds)
	targetEc2 := ec2.NewFromConfig(targetCfg)
	ready := false
	for i := 0; i < 40; i++ { // wait up to 10 mins
		<-ticker.C
		// 尝试调用新区域的 API，测试权限是否真正可用
		_, err := targetEc2.DescribeVpcs(ctx, &ec2.DescribeVpcsInput{})
		if err == nil {
			ready = true
			fmt.Println("\n✅ 新区域 API 权限已完全就绪！")
			break
		} else if strings.Contains(err.Error(), "AuthFailure") || strings.Contains(err.Error(), "UnauthorizedOperation") {
			fmt.Print("a") // Authentication failed (not fully synced)
		} else if strings.Contains(err.Error(), "OptInRequired") {
			fmt.Print("o") // Still requires opt-in logic to process
		} else {
			fmt.Print(".") // DNS or other spin-up lag
		}
	}
	if !ready {
		fmt.Println("\n⚠️ 区域 API 可能仍未完全就绪，将尝试继续，如果遇到报错请等几分钟后再试。")
	}
	return nil
}

// 修复点 2：为新开通的区域创建默认 VPC
func ensureDefaultVpc(ctx context.Context, cli *ec2.Client) (string, error) {
	vpcs, err := cli.DescribeVpcs(ctx, &ec2.DescribeVpcsInput{Filters: []ec2t.Filter{{Name: aws.String("isDefault"), Values: []string{"true"}}}})
	if err == nil && len(vpcs.Vpcs) > 0 {
		return *vpcs.Vpcs[0].VpcId, nil
	}
	fmt.Println("⏳ 该区域尚未初始化网络，正在创建默认 VPC...")
	out, err := cli.CreateDefaultVpc(ctx, &ec2.CreateDefaultVpcInput{})
	if err != nil {
		return "", fmt.Errorf("创建默认 VPC 失败: %v", err)
	}
	fmt.Println("✅ 默认 VPC 创建成功:", *out.Vpc.VpcId)
	return *out.Vpc.VpcId, nil
}

func checkQuotas(ctx context.Context, creds aws.CredentialsProvider) {
	cfg, err := mkCfg(ctx, "us-east-1", creds)
	if err != nil {
		fmt.Println("❌ 失败:", err)
		return
	}
	fmt.Println("\n正在查询.....")
	sqCli := servicequotas.NewFromConfig(cfg)
	vcpuCode := "L-1216C47A"
	svcCode := "ec2"
	qOut, err := sqCli.GetServiceQuota(ctx, &servicequotas.GetServiceQuotaInput{ServiceCode: &svcCode, QuotaCode: &vcpuCode})
	if err != nil {
		fmt.Printf("EC2配额: 失败\n")
	} else {
		fmt.Printf("EC2配额: %.0f vCPU\n", *qOut.Quota.Value)
	}
	input("\n按回车返回...", "")
}

func autoSetupIPv6(ctx context.Context, cli *ec2.Client, region, vpcID, targetSubnetID string) (string, error) {
	fmt.Println("🔍 配置 IPv6 (VPC/子网)...")
	vpcOut, err := cli.DescribeVpcs(ctx, &ec2.DescribeVpcsInput{VpcIds: []string{vpcID}})
	if err != nil {
		return "", err
	}
	hasVpcIPv6 := false
	var vpcCidrBlock string
	for _, assoc := range vpcOut.Vpcs[0].Ipv6CidrBlockAssociationSet {
		if assoc.Ipv6CidrBlockState.State == ec2t.VpcCidrBlockStateCodeAssociated {
			hasVpcIPv6 = true
			vpcCidrBlock = *assoc.Ipv6CidrBlock
			break
		}
	}
	if !hasVpcIPv6 {
		_, err := cli.AssociateVpcCidrBlock(ctx, &ec2.AssociateVpcCidrBlockInput{
			VpcId: aws.String(vpcID), AmazonProvidedIpv6CidrBlock: aws.Bool(true),
		})
		if err != nil {
			return "", err
		}
		fmt.Println("   -> 申请 VPC IPv6 成功")
		for i := 0; i < 10; i++ {
			time.Sleep(3 * time.Second)
			v, _ := cli.DescribeVpcs(ctx, &ec2.DescribeVpcsInput{VpcIds: []string{vpcID}})
			for _, a := range v.Vpcs[0].Ipv6CidrBlockAssociationSet {
				if a.Ipv6CidrBlockState.State == ec2t.VpcCidrBlockStateCodeAssociated {
					vpcCidrBlock = *a.Ipv6CidrBlock
					goto VPC_READY
				}
			}
		}
		return "", fmt.Errorf("超时")
	}
VPC_READY:
	// 获取子网
	var subOut *ec2.DescribeSubnetsOutput
	if targetSubnetID != "" {
		subOut, err = cli.DescribeSubnets(ctx, &ec2.DescribeSubnetsInput{SubnetIds: []string{targetSubnetID}})
	} else {
		subOut, err = cli.DescribeSubnets(ctx, &ec2.DescribeSubnetsInput{Filters: []ec2t.Filter{{Name: aws.String("vpc-id"), Values: []string{vpcID}}}})
	}

	if err != nil || len(subOut.Subnets) == 0 {
		return "", fmt.Errorf("无子网")
	}

	subnet := subOut.Subnets[0]
	subnetID := *subnet.SubnetId

	// 检查子网是否已有 IPv6
	hasSubnetIPv6 := false
	for _, assoc := range subnet.Ipv6CidrBlockAssociationSet {
		if assoc.Ipv6CidrBlockState.State == ec2t.SubnetCidrBlockStateCodeAssociated {
			hasSubnetIPv6 = true
			break
		}
	}

	if !hasSubnetIPv6 {
		newSubnetCidr := strings.Replace(vpcCidrBlock, "/56", "/64", 1)
		_, err = cli.AssociateSubnetCidrBlock(ctx, &ec2.AssociateSubnetCidrBlockInput{SubnetId: aws.String(subnetID), Ipv6CidrBlock: aws.String(newSubnetCidr)})
		if err != nil {
			if strings.Contains(err.Error(), "Conflict") {
				return "", fmt.Errorf("IPv6网段分配冲突，请手动在控制台配置子网 CIDR")
			}
			return "", err
		}
		fmt.Println("   -> 子网关联 IPv6 CIDR 成功")
	}

	cli.ModifySubnetAttribute(ctx, &ec2.ModifySubnetAttributeInput{
		SubnetId: aws.String(subnetID), AssignIpv6AddressOnCreation: &ec2t.AttributeBooleanValue{Value: aws.Bool(true)},
	})

	// Route
	rtOut, err := cli.DescribeRouteTables(ctx, &ec2.DescribeRouteTablesInput{Filters: []ec2t.Filter{{Name: aws.String("vpc-id"), Values: []string{vpcID}}}})
	if err == nil && len(rtOut.RouteTables) > 0 {
		var targetRT *ec2t.RouteTable
		for _, rt := range rtOut.RouteTables {
			for _, assoc := range rt.Associations {
				if assoc.SubnetId != nil && *assoc.SubnetId == subnetID {
					targetRT = &rt
					goto FOUND_RT
				}
			}
		}
		if targetRT == nil {
			for _, rt := range rtOut.RouteTables {
				for _, assoc := range rt.Associations {
					if assoc.Main != nil && *assoc.Main {
						targetRT = &rt
						goto FOUND_RT
					}
				}
			}
		}

	FOUND_RT:
		if targetRT != nil {
			hasRoute := false
			var igwID string
			igwOut, _ := cli.DescribeInternetGateways(ctx, &ec2.DescribeInternetGatewaysInput{Filters: []ec2t.Filter{{Name: aws.String("attachment.vpc-id"), Values: []string{vpcID}}}})
			if len(igwOut.InternetGateways) > 0 {
				igwID = *igwOut.InternetGateways[0].InternetGatewayId
			}
			for _, r := range targetRT.Routes {
				if aws.ToString(r.DestinationIpv6CidrBlock) == "::/0" {
					hasRoute = true
					break
				}
			}
			if !hasRoute && igwID != "" {
				cli.CreateRoute(ctx, &ec2.CreateRouteInput{
					RouteTableId: targetRT.RouteTableId, DestinationIpv6CidrBlock: aws.String("::/0"), GatewayId: aws.String(igwID),
				})
				fmt.Println("   -> 路由表更新成功 (::/0 -> IGW)")
			}
		}
	}
	return subnetID, nil
}

// 修改参数：直接传入 vpcID 避免重复查询
func ensureOpenAllSG(ctx context.Context, cli *ec2.Client, vpcID string) (string, error) {
	if vpcID == "" {
		return "", fmt.Errorf("VPC ID 不能为空")
	}
	sgName := "open-all-ports"
	sgs, _ := cli.DescribeSecurityGroups(ctx, &ec2.DescribeSecurityGroupsInput{
		Filters: []ec2t.Filter{{Name: aws.String("group-name"), Values: []string{sgName}}, {Name: aws.String("vpc-id"), Values: []string{vpcID}}},
	})
	if len(sgs.SecurityGroups) > 0 {
		return *sgs.SecurityGroups[0].GroupId, nil
	}
	res, err := cli.CreateSecurityGroup(ctx, &ec2.CreateSecurityGroupInput{GroupName: aws.String(sgName), Description: aws.String("Auto generated"), VpcId: aws.String(vpcID)})
	if err != nil {
		return "", err
	}
	cli.AuthorizeSecurityGroupIngress(ctx, &ec2.AuthorizeSecurityGroupIngressInput{
		GroupId: res.GroupId,
		IpPermissions: []ec2t.IpPermission{
			{IpProtocol: aws.String("-1"), IpRanges: []ec2t.IpRange{{CidrIp: aws.String("0.0.0.0/0")}}},
			{IpProtocol: aws.String("-1"), Ipv6Ranges: []ec2t.Ipv6Range{{CidrIpv6: aws.String("::/0")}}},
		},
	})
	return *res.GroupId, nil
}

// 修复点 3：增加错误打印，防止被静默跳过
func getLatestAMIWithArch(ctx context.Context, cli *ec2.Client, owner, namePattern, arch string) string {
	out, err := cli.DescribeImages(ctx, &ec2.DescribeImagesInput{
		Owners: []string{owner},
		Filters: []ec2t.Filter{
			{Name: aws.String("name"), Values: []string{namePattern}},
			{Name: aws.String("architecture"), Values: []string{arch}},
			{Name: aws.String("virtualization-type"), Values: []string{"hvm"}},
		},
	})
	if err != nil {
		fmt.Printf("\n[错误] 查询 AMI 失败 (可能是新区域 API 尚未完全同步): %v\n", err)
		return ""
	}
	if len(out.Images) == 0 {
		fmt.Printf("\n[错误] 该区域未找到匹配的 AMI (Owner: %s)\n", owner)
		return ""
	}
	sort.Slice(out.Images, func(i, j int) bool { return *out.Images[i].CreationDate > *out.Images[j].CreationDate })
	return *out.Images[0].ImageId
}

func ec2Create(ctx context.Context, regions []RegionInfo, creds aws.CredentialsProvider) {
	fmt.Println("\n请选择 CPU 架构:")
	fmt.Println("  1) x86_64 (Intel/AMD) [默认]")
	fmt.Println("  2) arm64 (Graviton)")
	archSel := input("请输入编号 [1]: ", "1")
	targetArch := "x86_64"
	if archSel == "2" {
		targetArch = "arm64"
	}

	regionInfo, err := pickRegion("\n选择 EC2 Region：", regions, "us-east-1")
	if err != nil {
		return
	}
	if err := ensureRegionOptIn(ctx, regionInfo.Name, regionInfo.Status, creds); err != nil {
		fmt.Println("❌ 区域不可用:", err)
		return
	}
	region := regionInfo.Name
	cfg, _ := mkCfg(ctx, region, creds)
	cli := ec2.NewFromConfig(cfg)

	// 新区域必备：提前初始化默认 VPC 网络
	vpcID, err := ensureDefaultVpc(ctx, cli)
	if err != nil {
		fmt.Println("❌ 初始化网络(VPC)失败:", err)
		return
	}

	// AMI List
	amiList := []AMIOption{
		{"Debian 12", "136693071363", "debian-12-*"},
		{"Debian 11", "136693071363", "debian-11-*"},
		{"Ubuntu 24.04", "099720109477", "ubuntu/images/hvm-ssd-gp3/ubuntu-noble-24.04-*"},
		{"Ubuntu 22.04", "099720109477", "ubuntu/images/hvm-ssd/ubuntu-jammy-22.04-*"},
		{"Amazon Linux 2023", "137112412989", "al2023-ami-2023.*"},
		{"Amazon Linux 2", "137112412989", "amzn2-ami-hvm-*"},
	}

	fmt.Printf("\n请选择操作系统 (%s):\n", targetArch)
	for i, a := range amiList {
		fmt.Printf("  %2d) %s\n", i+1, a.Name)
	}
	fmt.Println("  99) 自定义 AMI ID")

	var ami string
	sel := input("请输入编号 [1]: ", "1")
	if sel == "99" {
		ami = input("请输入 AMI ID: ", "")
	} else {
		idx := mustInt(sel)
		if idx > 0 && idx <= len(amiList) {
			target := amiList[idx-1]
			fmt.Printf("🔍 正在搜索 %s (%s) 的最新镜像...\n", target.Name, targetArch)
			ami = getLatestAMIWithArch(ctx, cli, target.Owner, target.Pattern, targetArch)
		} else {
			fmt.Println("❌ 编号无效")
			return
		}
	}
	if ami == "" {
		fmt.Println("❌ 未找到有效 AMI，终止创建")
		return
	}
	fmt.Println("✅ 选中 AMI:", ami)

	// Type
	var typeList []TypeOption
	if targetArch == "x86_64" {
		typeList = []TypeOption{{"t2.nano", "1 vCPU, 0.5 GiB"}, {"t2.micro", "1 vCPU, 1.0 GiB"}, {"t3.micro", "2 vCPU, 1.0 GiB"}}
	} else {
		typeList = []TypeOption{{"t4g.nano", "2 vCPU, 0.5 GiB"}, {"t4g.micro", "2 vCPU, 1.0 GiB"}}
	}
	fmt.Printf("\n请选择实例类型:\n")
	for i, t := range typeList {
		fmt.Printf("  %2d) %s\n", i+1, t.Type)
	}
	var itype string
	tSel := input("编号 [1]: ", "1")
	idx := mustInt(tSel)
	if idx > 0 && idx <= len(typeList) {
		itype = typeList[idx-1].Type
	} else {
		itype = typeList[0].Type
	}

	count := int32(mustInt(input("启动数量 [1]: ", "1")))
	if count < 1 {
		count = 1
	}
	volSize := int32(mustInt(input("磁盘大小(GB) [默认]: ", "0")))
	enableIPv6 := yes(input("自动分配 IPv6? [y/N]: ", "n"))
	rootPwd := input("设置 SSH root 密码 (留空跳过): ", "")
	openAll := yes(input("全开端口 (安全组)? [y/N]: ", "n"))

	rawUD, empty := collectUserData("\n可选：EC2 启动脚本")
	userData := ""
	if rootPwd != "" {
		userData = fmt.Sprintf("#!/bin/bash\necho \"root:%s\" | chpasswd\n", rootPwd)
		userData += "sed -i 's/^#PermitRootLogin.*/PermitRootLogin yes/' /etc/ssh/sshd_config\n"
		userData += "sed -i 's/^#PasswordAuthentication.*/PasswordAuthentication yes/' /etc/ssh/sshd_config\n"
		userData += "service sshd restart\n"
		if !empty {
			userData += "\n" + rawUD
		}
	} else if !empty {
		userData = rawUD
	}

	var sgID string
	if openAll || enableIPv6 {
		s, err := ensureOpenAllSG(ctx, cli, vpcID)
		if err != nil {
			fmt.Println("❌ 配置安全组失败:", err)
			return
		}
		sgID = s
	}

	var targetSubnetID string
	if enableIPv6 {
		sID, err := autoSetupIPv6(ctx, cli, region, vpcID, "")
		if err != nil {
			fmt.Println("⚠️ IPv6 配置失败:", err)
			enableIPv6 = false
		} else {
			targetSubnetID = sID
		}
	}

	runIn := &ec2.RunInstancesInput{
		ImageId:      aws.String(ami),
		InstanceType: ec2t.InstanceType(itype),
		MinCount:     aws.Int32(count),
		MaxCount:     aws.Int32(count),
	}
	
	if userData != "" {
		runIn.UserData = aws.String(base64.StdEncoding.EncodeToString([]byte(userData)))
	}
	
	if enableIPv6 || sgID != "" {
		netIf := ec2t.InstanceNetworkInterfaceSpecification{DeviceIndex: aws.Int32(0), AssociatePublicIpAddress: aws.Bool(true)}
		if sgID != "" {
			netIf.Groups = []string{sgID}
		}
		if enableIPv6 {
			netIf.Ipv6AddressCount = aws.Int32(1)
			netIf.SubnetId = aws.String(targetSubnetID)
		} else {
			// 如果没开 IPv6，但配置了安全组，也需要明确指定 VPC 默认的子网，否则可能会报错
			subOut, err := cli.DescribeSubnets(ctx, &ec2.DescribeSubnetsInput{Filters: []ec2t.Filter{{Name: aws.String("vpc-id"), Values: []string{vpcID}}}})
			if err == nil && len(subOut.Subnets) > 0 {
				netIf.SubnetId = subOut.Subnets[0].SubnetId
			}
		}
		runIn.NetworkInterfaces = []ec2t.InstanceNetworkInterfaceSpecification{netIf}
	}
	if volSize > 0 {
		imgOut, _ := cli.DescribeImages(ctx, &ec2.DescribeImagesInput{ImageIds: []string{ami}})
		if len(imgOut.Images) > 0 {
			runIn.BlockDeviceMappings = []ec2t.BlockDeviceMapping{{
				DeviceName: imgOut.Images[0].RootDeviceName,
				Ebs:        &ec2t.EbsBlockDevice{VolumeSize: aws.Int32(volSize), VolumeType: ec2t.VolumeTypeGp3},
			}}
		}
	}

	fmt.Printf("\n🚀 正在启动 %d 台...\n", count)
	out, err := cli.RunInstances(ctx, runIn)
	if err != nil {
		fmt.Println("❌ 失败:", err)
		return
	}
	for _, ins := range out.Instances {
		fmt.Println("✅ 成功:", *ins.InstanceId)
	}
}

func lsListAll(ctx context.Context, regions []string, creds aws.CredentialsProvider) ([]LSInstanceRow, error) {
	var (
		mu   sync.Mutex
		rows = make([]LSInstanceRow, 0, 8)
		wg   sync.WaitGroup
	)
	fmt.Printf("正在并发扫描 %d 个 Lightsail 区域...\n", len(regions))
	for _, rg := range regions {
		wg.Add(1)
		go func(region string) {
			defer wg.Done()
			cfg, err := mkCfg(ctx, region, creds)
			if err != nil {
				return
			}
			cli := lightsail.NewFromConfig(cfg)
			out, err := cli.GetInstances(ctx, &lightsail.GetInstancesInput{})
			if err != nil || len(out.Instances) == 0 {
				return
			}
			var localRows []LSInstanceRow
			for _, ins := range out.Instances {
				ip := ""
				if ins.PublicIpAddress != nil {
					ip = *ins.PublicIpAddress
				}
				ipv6 := ""
				if len(ins.Ipv6Addresses) > 0 {
					ipv6 = ins.Ipv6Addresses[0]
				}
				state := ""
				if ins.State != nil {
					state = aws.ToString(ins.State.Name)
				}
				az := ""
				if ins.Location != nil {
					az = aws.ToString(ins.Location.AvailabilityZone)
				}
				bundle := ""
				if ins.BundleId != nil {
					bundle = *ins.BundleId
				}
				localRows = append(localRows, LSInstanceRow{
					Region: region, Name: aws.ToString(ins.Name), State: state, IP: ip, IPv6: ipv6, AZ: az, Bundle: bundle,
				})
			}
			mu.Lock()
			rows = append(rows, localRows...)
			mu.Unlock()
		}(rg)
	}
	wg.Wait()
	sort.Slice(rows, func(i, j int) bool { return rows[i].Region < rows[j].Region })
	for i := range rows {
		rows[i].Idx = i + 1
	}
	return rows, nil
}

func lsCreate(ctx context.Context, regions []string, creds aws.CredentialsProvider) {
	region, err := pickFromList("\n选择 Lightsail Region：", regions, "us-east-1")
	if err != nil {
		return
	}
	cfg, _ := mkCfg(ctx, region, creds)
	cli := lightsail.NewFromConfig(cfg)
	az := input("可用区 (默认自动): ", region+"a")
	name := input("实例名称 [LS-1]: ", "LS-1")
	bOut, _ := cli.GetBundles(ctx, &lightsail.GetBundlesInput{})
	type bRow struct {
		ID    string
		Price float64
		Ram   float64
		Cpu   int32
	}
	var brs []bRow
	defBundle := "nano_3_0"
	defIdx := 1
	for _, b := range bOut.Bundles {
		if b.IsActive != nil && !*b.IsActive {
			continue
		}
		if b.SupportedPlatforms != nil && len(b.SupportedPlatforms) > 0 && b.SupportedPlatforms[0] == lst.InstancePlatformWindows {
			continue
		}
		brs = append(brs, bRow{ID: *b.BundleId, Price: float64(*b.Price), Ram: float64(*b.RamSizeInGb), Cpu: *b.CpuCount})
	}
	sort.Slice(brs, func(i, j int) bool { return brs[i].Price < brs[j].Price })
	for i, b := range brs {
		if b.ID == defBundle {
			defIdx = i + 1
			break
		}
	}
	fmt.Println("--- 套餐列表 ---")
	printTable("NO.\tID\tPrice\tRAM\tCPU", func(w *tabwriter.Writer) {
		for i, b := range brs {
			mk := ""; if i+1 == defIdx { mk = " <-- 默认" }
			fmt.Fprintf(w, "[%d]\t%s\t$%.2f\t%.1f G\t%d vCPU%s\n", i+1, b.ID, b.Price, b.Ram, b.Cpu, mk)
		}
	})
	bIn := input(fmt.Sprintf("输入套餐序号 (默认 %d): ", defIdx), "")
	finalBundle := brs[defIdx-1].ID
	if idx, err := strconv.Atoi(bIn); err == nil && idx > 0 && idx <= len(brs) {
		finalBundle = brs[idx-1].ID
	}
	pOut, _ := cli.GetBlueprints(ctx, &lightsail.GetBlueprintsInput{})
	var osList []string
	defOSIdx := 1
	for _, p := range pOut.Blueprints {
		if p.Platform == lst.InstancePlatformLinuxUnix {
			osList = append(osList, *p.BlueprintId)
		}
	}
	sort.Strings(osList)
	fmt.Println("\n--- 系统列表 ---")
	for i, os := range osList {
		mk := ""; if os == "debian_12" { mk = " <-- 默认"; defOSIdx = i + 1 }
		fmt.Printf("[%d] %s%s\n", i+1, os, mk)
	}
	oIn := input(fmt.Sprintf("输入系统序号 (默认 %d): ", defOSIdx), "")
	finalOS := osList[defOSIdx-1]
	if idx, err := strconv.Atoi(oIn); err == nil && idx > 0 && idx <= len(osList) {
		finalOS = osList[idx-1]
	}
	openAll := yes(input("是否全开防火墙端口 (TCP+UDP 0-65535)? [y/N]: ", "n"))
	ud, _ := collectUserData("\n可选：UserData 脚本")
	fmt.Println("🚀 创建中...")
	_, err = cli.CreateInstances(ctx, &lightsail.CreateInstancesInput{
		AvailabilityZone: aws.String(az), BlueprintId: aws.String(finalOS), BundleId: aws.String(finalBundle),
		InstanceNames: []string{name}, UserData: aws.String(ud),
	})
	if err != nil {
		fmt.Println("❌ 失败:", err)
		return
	}
	fmt.Println("✅ 实例创建指令已提交")
	if openAll {
		fmt.Println("⏳ 正在等待实例就绪以配置防火墙 (最多等待 60 秒)...")
		ready := false
		for i := 0; i < 30; i++ {
			time.Sleep(2 * time.Second)
			insOut, err := cli.GetInstance(ctx, &lightsail.GetInstanceInput{InstanceName: aws.String(name)})
			if err == nil && insOut.Instance != nil && insOut.Instance.State != nil {
				if aws.ToString(insOut.Instance.State.Name) == "running" {
					ready = true
					break
				}
			}
			fmt.Print(".")
		}
		if ready {
			fmt.Println("\n✅ 实例已就绪，正在开启端口...")
			cli.PutInstancePublicPorts(ctx, &lightsail.PutInstancePublicPortsInput{
				InstanceName: aws.String(name),
				PortInfos: []lst.PortInfo{
					{FromPort: 0, ToPort: 65535, Protocol: lst.NetworkProtocolTcp},
					{FromPort: 0, ToPort: 65535, Protocol: lst.NetworkProtocolUdp},
				},
			})
			fmt.Println("✅ 防火墙规则已更新 (全开)")
		} else {
			fmt.Println("\n⚠️ 等待超时，请稍后手动配置防火墙。")
		}
	}
}

func lsControl(ctx context.Context, regions []string, creds aws.CredentialsProvider) {
	rows, _ := lsListAll(ctx, regions, creds)
	if len(rows) == 0 {
		fmt.Println("❌ 无实例")
		return
	}
	printTable("序号\t区域\t名称\t状态\t配置\tIPv4\tIPv6", func(w *tabwriter.Writer) {
		for _, r := range rows {
			fmt.Fprintf(w, "%d\t%s\t%s\t%s\t%s\t%s\t%s\n", r.Idx, r.Region, r.Name, r.State, cut(r.Bundle, 10), r.IP, r.IPv6)
		}
	})
	idx := mustInt(input("\n输入序号操作 (0 返回): ", "0"))
	if idx <= 0 || idx > len(rows) {
		return
	}
	sel := rows[idx-1]
	cfg, _ := mkCfg(ctx, sel.Region, creds)
	cli := lightsail.NewFromConfig(cfg)
	fmt.Printf("\n🔍 正在获取 Lightsail 实例 %s 的详细指标...\n", sel.Name)
	insOut, err := cli.GetInstance(ctx, &lightsail.GetInstanceInput{InstanceName: &sel.Name})
	var isStaticIP bool
	if err == nil && insOut.Instance != nil {
		ins := insOut.Instance
		isStaticIP = *ins.IsStaticIp
		var ports []string
		for _, p := range ins.Networking.Ports {
			if (p.FromPort == 0 && p.ToPort == 65535) || (p.FromPort == 0 && (p.Protocol == "all" || p.Protocol == "-1")) {
				ports = append(ports, fmt.Sprintf("全部允许 (%s)", p.Protocol))
			} else {
				ports = append(ports, fmt.Sprintf("%d/%s", p.FromPort, p.Protocol))
			}
		}
		fmt.Println("================================================================")
		fmt.Printf(" 实例名称  : %s\n", *ins.Name)
		fmt.Printf(" 所在区域  : %s (%s)\n", sel.Region, *ins.Location.AvailabilityZone)
		fmt.Printf(" 套餐类型  : %s (%d vCPU, %.1f GB RAM)\n", *ins.BundleId, *ins.Hardware.CpuCount, *ins.Hardware.RamSizeInGb)
		fmt.Printf(" 运行状态  : %s\n", *ins.State.Name)
		fmt.Printf(" 公网 IPv4 : %s\n", sel.IP)
		fmt.Printf(" IP 类型   : %v\n", func() string {
			if isStaticIP {
				return "[固定IP/Static] ✅"
			}
			return "[动态IP/Dynamic]"
		}())
		fmt.Printf(" 开放端口  : %s\n", strings.Join(ports, ", "))
		fmt.Println("================================================================")
	}
	fmt.Printf("\n操作: %s\n1) 启动 2) 停止 3) 重启 4) 删除 5) 管理固定 IP\n", sel.Name)
	switch input("选择: ", "0") {
	case "1":
		cli.StartInstance(ctx, &lightsail.StartInstanceInput{InstanceName: &sel.Name})
		fmt.Println("✅ 启动中")
	case "2":
		cli.StopInstance(ctx, &lightsail.StopInstanceInput{InstanceName: &sel.Name})
		fmt.Println("✅ 停止中")
	case "3":
		cli.RebootInstance(ctx, &lightsail.RebootInstanceInput{InstanceName: &sel.Name})
		fmt.Println("✅ 重启中")
	case "4":
		if yes(input("⚠️ 确认删除实例 (删除)? [y/N]: ", "n")) {
			fmt.Println("🔍 检查固定 IP...")
			allSip, err := cli.GetStaticIps(ctx, &lightsail.GetStaticIpsInput{})
			if err == nil {
				for _, s := range allSip.StaticIps {
					if s.AttachedTo != nil && *s.AttachedTo == sel.Name {
						fmt.Printf("⚠️ 释放关联 IP (%s)...\n", *s.Name)
						cli.ReleaseStaticIp(ctx, &lightsail.ReleaseStaticIpInput{StaticIpName: s.Name})
						break
					}
				}
			}
			cli.DeleteInstance(ctx, &lightsail.DeleteInstanceInput{InstanceName: &sel.Name})
			fmt.Println("🗑️ 删除指令已发送")
		}
	case "5":
		if isStaticIP {
			if yes(input("是否解绑并释放当前固定 IP? [y/N]: ", "n")) {
				allSip, _ := cli.GetStaticIps(ctx, &lightsail.GetStaticIpsInput{})
				for _, s := range allSip.StaticIps {
					if s.AttachedTo != nil && *s.AttachedTo == sel.Name {
						ipName := *s.Name
						cli.DetachStaticIp(ctx, &lightsail.DetachStaticIpInput{StaticIpName: &ipName})
						fmt.Println("✅ 已解绑")
						cli.ReleaseStaticIp(ctx, &lightsail.ReleaseStaticIpInput{StaticIpName: &ipName})
						fmt.Println("🗑️ 已释放")
						break
					}
				}
			}
		} else {
			if yes(input("是否申请并绑定新固定 IP? [y/N]: ", "n")) {
				newIpName := fmt.Sprintf("Static-%s", sel.Name)
				cli.AllocateStaticIp(ctx, &lightsail.AllocateStaticIpInput{StaticIpName: &newIpName})
				cli.AttachStaticIp(ctx, &lightsail.AttachStaticIpInput{InstanceName: &sel.Name, StaticIpName: &newIpName})
				fmt.Println("✅ 绑定成功")
			}
		}
	}
}

func ec2ListAll(ctx context.Context, regions []string, creds aws.CredentialsProvider) ([]EC2InstanceRow, error) {
	var mu sync.Mutex
	var rows []EC2InstanceRow
	var wg sync.WaitGroup
	fmt.Printf("正在并发扫描 %d 个 EC2 区域...\n", len(regions))
	for _, rg := range regions {
		wg.Add(1)
		go func(region string) {
			defer wg.Done()
			cfg, err := mkCfg(ctx, region, creds)
			if err != nil {
				return
			}
			cli := ec2.NewFromConfig(cfg)
			out, err := cli.DescribeInstances(ctx, &ec2.DescribeInstancesInput{})
			if err != nil {
				return
			}
			var local []EC2InstanceRow
			for _, res := range out.Reservations {
				for _, ins := range res.Instances {
					if ins.State.Name == ec2t.InstanceStateNameTerminated {
						continue
					}
					name := ""
					for _, t := range ins.Tags {
						if *t.Key == "Name" {
							name = *t.Value
						}
					}
					pub := ""
					if ins.PublicIpAddress != nil {
						pub = *ins.PublicIpAddress
					}
					priv := ""
					if ins.PrivateIpAddress != nil {
						priv = *ins.PrivateIpAddress
					}
					ipv6 := ""
					if len(ins.NetworkInterfaces) > 0 && len(ins.NetworkInterfaces[0].Ipv6Addresses) > 0 {
						ipv6 = *ins.NetworkInterfaces[0].Ipv6Addresses[0].Ipv6Address
					}
					local = append(local, EC2InstanceRow{
						Region: region, ID: *ins.InstanceId, State: string(ins.State.Name),
						Name: name, Type: string(ins.InstanceType), PubIP: pub, PrivIP: priv, IPv6: ipv6,
					})
				}
			}
			mu.Lock()
			rows = append(rows, local...)
			mu.Unlock()
		}(rg)
	}
	wg.Wait()
	sort.Slice(rows, func(i, j int) bool { return rows[i].Region < rows[j].Region })
	for i := range rows {
		rows[i].Idx = i + 1
	}
	return rows, nil
}

func ec2Control(ctx context.Context, regions []string, creds aws.CredentialsProvider) {
	rows, _ := ec2ListAll(ctx, regions, creds)
	if len(rows) == 0 {
		fmt.Println("❌ 无实例")
		return
	}
	printTable("序号\t区域\tID\t名称\t状态\t配置\t公网IP\t内网IP\tIPv6", func(w *tabwriter.Writer) {
		for _, r := range rows {
			fmt.Fprintf(w, "%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n",
				r.Idx, r.Region, r.ID, cut(r.Name, 10), r.State, r.Type, r.PubIP, r.PrivIP, r.IPv6)
		}
	})
	idx := mustInt(input("\n输入序号操作 (0 返回): ", "0"))
	if idx <= 0 || idx > len(rows) {
		return
	}
	sel := rows[idx-1]
	cfg, _ := mkCfg(ctx, sel.Region, creds)
	cli := ec2.NewFromConfig(cfg)
	fmt.Printf("\n🔍 正在获取实例 %s 的详细指标 (磁盘/网络/密钥)...\n", sel.ID)
	desc, err := cli.DescribeInstances(ctx, &ec2.DescribeInstancesInput{InstanceIds: []string{sel.ID}})
	
	// 用于保存主网卡ID和当前IPv6列表，供后续操作使用
	var eniID string
	var currentIPv6s []string
	var vpcID, subnetID string

	if err == nil && len(desc.Reservations) > 0 {
		ins := desc.Reservations[0].Instances[0]
		vpcID = *ins.VpcId
		subnetID = *ins.SubnetId

		var diskInfo []string
		for _, bd := range ins.BlockDeviceMappings {
			if bd.Ebs != nil {
				volID := *bd.Ebs.VolumeId
				vOut, err := cli.DescribeVolumes(ctx, &ec2.DescribeVolumesInput{VolumeIds: []string{volID}})
				if err == nil && len(vOut.Volumes) > 0 {
					diskInfo = append(diskInfo, fmt.Sprintf("%s [%d GB %s]", *bd.DeviceName, *vOut.Volumes[0].Size, vOut.Volumes[0].VolumeType))
				}
			}
		}

		// 获取主网卡信息
		if len(ins.NetworkInterfaces) > 0 {
			eniID = *ins.NetworkInterfaces[0].NetworkInterfaceId
			for _, addr := range ins.NetworkInterfaces[0].Ipv6Addresses {
				currentIPv6s = append(currentIPv6s, *addr.Ipv6Address)
			}
		}

		fmt.Println("================================================================")
		fmt.Printf(" 实例 ID   : %s\n", *ins.InstanceId)
		fmt.Printf(" 所在区域  : %s (%s)\n", sel.Region, *ins.Placement.AvailabilityZone)
		fmt.Printf(" 实例类型  : %s\n", ins.InstanceType)
		fmt.Printf(" 运行状态  : %s\n", ins.State.Name)
		fmt.Printf(" 公网 IPv4 : %s\n", sel.PubIP)
		fmt.Printf(" 内网 IPv4 : %s\n", sel.PrivIP)
		if len(currentIPv6s) > 0 {
			fmt.Printf(" IPv6 地址 : %s\n", strings.Join(currentIPv6s, ", "))
		} else {
			fmt.Printf(" IPv6 地址 : (未分配)\n")
		}
		fmt.Printf(" 启动时间  : %s\n", ins.LaunchTime.Format("2006-01-02 15:04:05"))
		if ins.KeyName != nil {
			fmt.Printf(" SSH 密钥  : %s\n", *ins.KeyName)
		}
		fmt.Printf(" 磁盘挂载  : %s\n", strings.Join(diskInfo, ", "))
		fmt.Println("================================================================")
	}

	fmt.Printf("\n操作: %s\n1) 启动 2) 停止 3) 重启 4) 终止 5) 🔧 网络管理 (IP)\n", sel.ID)
	switch input("选择: ", "0") {
	case "1":
		cli.StartInstances(ctx, &ec2.StartInstancesInput{InstanceIds: []string{sel.ID}})
		fmt.Println("✅ 启动中")
	case "2":
		cli.StopInstances(ctx, &ec2.StopInstancesInput{InstanceIds: []string{sel.ID}})
		fmt.Println("✅ 停止中")
	case "3":
		cli.RebootInstances(ctx, &ec2.RebootInstancesInput{InstanceIds: []string{sel.ID}})
		fmt.Println("✅ 重启中")
	case "4":
		if yes(input("⚠️ 确认终止实例 (删除)? [y/N]: ", "n")) {
			fmt.Println("🔍 检查关联EIP...")
			eipOut, err := cli.DescribeAddresses(ctx, &ec2.DescribeAddressesInput{
				Filters: []ec2t.Filter{{Name: aws.String("instance-id"), Values: []string{sel.ID}}},
			})
			if err == nil && len(eipOut.Addresses) > 0 {
				for _, addr := range eipOut.Addresses {
					cli.ReleaseAddress(ctx, &ec2.ReleaseAddressInput{AllocationId: addr.AllocationId})
					fmt.Printf("   ✅ 已释放 IP: %s\n", *addr.PublicIp)
				}
			}
			cli.TerminateInstances(ctx, &ec2.TerminateInstancesInput{InstanceIds: []string{sel.ID}})
			fmt.Println("🗑️ 正在终止...")
		}
	case "5":
		if eniID == "" {
			fmt.Println("❌ 无法找到网络接口 (ENI)，无法操作")
			return
		}
		fmt.Println("\n--- 网络/IP 管理 ---")
		fmt.Println(" 1) IPv6 管理 (分配/删除)")
		fmt.Println(" 2) IPv4 公网/弹性IP 管理 (绑定/释放)")
		netSel := input("选择: ", "0")

		if netSel == "1" {
			fmt.Printf("当前 IPv6: %v\n", currentIPv6s)
			fmt.Println(" 1) ➕ 分配新 IPv6")
			fmt.Println(" 2) ➖ 删除现有 IPv6")
			sub := input("选择: ", "0")
			if sub == "1" {
				_, err := cli.AssignIpv6Addresses(ctx, &ec2.AssignIpv6AddressesInput{
					NetworkInterfaceId: aws.String(eniID),
					Ipv6AddressCount:   aws.Int32(1),
				})
				if err != nil {
					if strings.Contains(err.Error(), "Subnet does not contain any IPv6 CIDR block ranges") {
						fmt.Println("\n⚠️  检测到子网未配置 IPv6，正在自动修复 (VPC/子网/路由)...")
						_, errFix := autoSetupIPv6(ctx, cli, sel.Region, vpcID, subnetID)
						if errFix != nil {
							fmt.Printf("❌ 修复失败: %v\n", errFix)
						} else {
							fmt.Println("✅ 网络配置已修复，正在重试分配 IP...")
							time.Sleep(2 * time.Second)
							_, errRetry := cli.AssignIpv6Addresses(ctx, &ec2.AssignIpv6AddressesInput{
								NetworkInterfaceId: aws.String(eniID),
								Ipv6AddressCount:   aws.Int32(1),
							})
							if errRetry != nil {
								fmt.Printf("❌ 重试分配失败: %v\n", errRetry)
							} else {
								fmt.Println("✅ 分配成功！(IP 可能需要几秒钟才会显示)")
							}
						}
					} else {
						fmt.Printf("❌ 分配失败: %v\n", err)
					}
				} else {
					fmt.Println("✅ 分配成功！(IP 可能需要几秒钟才会显示)")
				}
			} else if sub == "2" {
				if len(currentIPv6s) == 0 {
					fmt.Println("❌ 当前没有 IPv6 地址可删除")
					return
				}
				fmt.Println("请选择要删除的 IP:")
				for i, ip := range currentIPv6s {
					fmt.Printf(" %d) %s\n", i+1, ip)
				}
				delIdx := mustInt(input("编号: ", "0"))
				if delIdx > 0 && delIdx <= len(currentIPv6s) {
					targetIP := currentIPv6s[delIdx-1]
					_, err := cli.UnassignIpv6Addresses(ctx, &ec2.UnassignIpv6AddressesInput{
						NetworkInterfaceId: aws.String(eniID),
						Ipv6Addresses:      []string{targetIP},
					})
					if err != nil {
						fmt.Printf("❌ 删除失败: %v\n", err)
					} else {
						fmt.Printf("✅ 已删除: %s\n", targetIP)
					}
				}
			}
		} else if netSel == "2" {
			fmt.Println("\n--- 弹性公网 IP (Elastic IP) ---")
			eipOut, err := cli.DescribeAddresses(ctx, &ec2.DescribeAddressesInput{
				Filters: []ec2t.Filter{{Name: aws.String("instance-id"), Values: []string{sel.ID}}},
			})
			if err != nil {
				fmt.Println("❌ 查询失败:", err)
				return
			}
			
			hasEIP := len(eipOut.Addresses) > 0
			fmt.Printf("当前公网 IP: %s\n", sel.PubIP)
			if hasEIP {
				fmt.Println("状态: [✅ 已绑定弹性 IP]")
				for _, addr := range eipOut.Addresses {
					fmt.Printf(" - %s (AllocationId: %s)\n", *addr.PublicIp, *addr.AllocationId)
				}
			} else {
				fmt.Println("状态: [⚠️ 动态公网 IP (重启可能会变)]")
			}

			fmt.Println("\n 1) ➕ 申请并绑定新 EIP (收费/Static)")
			fmt.Println(" 2) ➖ 解绑并释放 EIP (省费)")
			
			sub := input("选择: ", "0")
			if sub == "1" {
				if hasEIP {
					fmt.Println("⚠️ 提示: 该实例已经绑定了弹性 IP。绑定多个可能需要配置辅助网卡。")
					if !yes(input("继续申请吗? [y/N]: ", "n")) {
						return
					}
				}
				fmt.Print("⏳ 正在申请 IP...")
				allocOut, err := cli.AllocateAddress(ctx, &ec2.AllocateAddressInput{Domain: ec2t.DomainTypeVpc})
				if err != nil {
					fmt.Println("\n❌ 申请失败:", err)
					return
				}
				newIP := *allocOut.PublicIp
				allocID := *allocOut.AllocationId
				fmt.Printf("成功! 获取到: %s\n", newIP)

				fmt.Print("⏳ 正在绑定...")
				_, err = cli.AssociateAddress(ctx, &ec2.AssociateAddressInput{
					InstanceId: aws.String(sel.ID),
					AllocationId: aws.String(allocID),
				})
				if err != nil {
					fmt.Printf("\n❌ 绑定失败: %v\n", err)
					fmt.Println("   正在回滚 (释放 IP)...")
					cli.ReleaseAddress(ctx, &ec2.ReleaseAddressInput{AllocationId: aws.String(allocID)})
				} else {
					fmt.Println("\n✅ 绑定成功！现在该实例拥有固定 IP。")
				}

			} else if sub == "2" {
				if !hasEIP {
					fmt.Println("❌ 当前没有绑定弹性 IP，无法释放。")
					return
				}
				target := eipOut.Addresses[0]
				fmt.Printf("即将释放 IP: %s\n", *target.PublicIp)
				if yes(input("确认解绑并释放? [y/N]: ", "n")) {
					if target.AssociationId != nil {
						_, err := cli.DisassociateAddress(ctx, &ec2.DisassociateAddressInput{
							AssociationId: target.AssociationId,
						})
						if err != nil {
							fmt.Println("❌ 解绑失败:", err)
							return
						}
						fmt.Println("✅ 已解绑")
					}
					_, err := cli.ReleaseAddress(ctx, &ec2.ReleaseAddressInput{
						AllocationId: target.AllocationId,
					})
					if err != nil {
						fmt.Println("❌ 释放失败 (IP可能仍被保留):", err)
					} else {
						fmt.Println("✅ 已释放 (停止计费)")
					}
				}
			}
		}
	}
}

// -------------------- Main --------------------

func main() {
	rand.Seed(time.Now().UnixNano())
	ctx := context.Background()
	fmt.Println("=== AWS 管理工具 (Win) ===")

	fmt.Println("\n请选择连接方式:")
	fmt.Println(" 1) 直连 (Direct Connection) [默认]")
	fmt.Println(" 2) 代理 (Use Proxy)")
	connType := input("选择 [1]: ", "1")

	if connType == "2" {
		rawProxy := input("请输入代理地址 (host:port:user:pass 或 socks5://...): ", "")
		GlobalProxy = parseProxyString(rawProxy)
		if GlobalProxy != "" {
			fmt.Println("🔄 使用代理:", GlobalProxy)
		}
	} else {
		fmt.Println("🌐 使用直连模式")
	}

	ak := input("AWS Access Key ID: ", "")
	sk := inputSecret("AWS Secret Access Key: ")
	if ak == "" || sk == "" {
		return
	}
	creds := credentials.NewStaticCredentialsProvider(ak, sk, "")

	fmt.Printf("\n🔍 验证凭证...\n")
	if err := stsCheck(ctx, bootstrapRegion, creds); err != nil {
		fmt.Println("❌ 失败:", err)
		return
	}
	fmt.Println("✅ 成功")

	fmt.Println("🌍 获取区域列表...")
	ec2Regions, _ := getEC2RegionsWithStatus(ctx, creds)
	lsRegions, _ := getLightsailRegions(ctx, creds)

	for {
		fmt.Println("\n====== 主菜单 ======")
		fmt.Println("1) EC2：创建 (自动AMI/IPv6/磁盘)")
		fmt.Println("2) EC2：管理 (全球扫描)")
		fmt.Println("3) Lightsail：创建")
		fmt.Println("4) Lightsail：管理")
		fmt.Println("5) 查询配额")
		fmt.Println("6) 💰 自动完成新手任务 (赚 $80)")
		fmt.Println("0) 退出")

		switch input("选择: ", "0") {
		case "1":
			ec2Create(ctx, ec2Regions, creds)
		case "2":
			var plainRegions []string
			for _, r := range ec2Regions {
				plainRegions = append(plainRegions, r.Name)
			}
			ec2Control(ctx, plainRegions, creds)
		case "3":
			lsCreate(ctx, lsRegions, creds)
		case "4":
			lsControl(ctx, lsRegions, creds)
		case "5":
			checkQuotas(ctx, creds)
		case "6":
			autoClaimCredits(ctx, creds)
		case "0":
			return
		}
	}
}
