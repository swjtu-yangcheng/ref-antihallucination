#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ref_verify.py —— 参考文献防幻觉核验脚本（纯标准库，零第三方依赖）

数据源：Crossref REST API（https://api.crossref.org，无需密钥）+ doi.org 解析。
用途：对文献列表逐条执行"题目—作者—期刊—年份—DOI"五要素交叉核对（Gate B），
      自动检测撤稿/更正记录（Gate D）、DOI 与题目级重复（Gate G），
      并可选核验正文引用与参考文献列表的一一对应关系（Gate H）。

用法：
  python ref_verify.py <文献列表文件>
  python ref_verify.py <文献列表文件> --body <正文文件>
  python ref_verify.py <文献列表文件> --report <核验报告.md>

文献列表文件格式：每行一条，允许行首编号（1. / 1、/ - / * 等）与 Markdown 链接语法。

判定状态：
  ✅ VERIFIED      五要素核验通过（或 DOI+题目双核验通过）
  ⚠️ CONFLICT      找到候选但存在字段冲突（报告列出冲突字段，须修正或删除）
  ❌ NOT_FOUND     Crossref 无匹配候选——英文文献视为存疑，按"宁缺毋滥"处理
  🔎 CNKI_CHANNEL  中文文献：Crossref 覆盖有限，转 CNKI/万方/谷歌学术人工核验
  📜 POLICY        政策文件：转发文机关官网核验全称与文号
  ⚠️ ERROR         网络或接口异常，转人工通道（WebSearch/WebFetch）

退出码：0 = 全部通过或仅需人工通道；1 = 存在 CONFLICT / NOT_FOUND（须处理）。
"""

import argparse
import difflib
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

CROSSREF = "https://api.crossref.org"
UA = "ref-antihallucination-skill/1.0 (https://api.crossref.org; mailto:ref-check@localhost)"
REQUEST_INTERVAL = 0.6  # 对 Crossref 的礼貌性限速（秒）

TITLE_SIM_PASS = 0.90   # 标题相似度 ≥ 此值视为匹配
TITLE_SIM_WEAK = 0.62   # 介于两者之间 → CONFLICT（疑似不匹配或解析偏差）
YEAR_TOL = 1            # 年份允许 ±1（在线优先出版与正式出版年份常差一年）


# ---------------------------------------------------------------- 基础工具

def http_get_json(url, timeout=30):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def doi_resolves(doi, timeout=20):
    """doi.org 是否可解析（覆盖 ChinaDOI 等非 Crossref 注册机构）。"""
    try:
        req = urllib.request.Request("https://doi.org/" + urllib.parse.quote(doi),
                                     headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.status < 400
    except Exception:
        return False


def norm_text(s):
    """归一化用于相似度比较：去标点、空白、统一小写。"""
    return re.sub(r"[\s\-–—_.,;:!?()'\"\[\]{}<>·、，。；：！？（）《》【】]", "", (s or "")).lower()


def sim(a, b):
    if not a or not b:
        return 0.0
    return difflib.SequenceMatcher(None, norm_text(a), norm_text(b)).ratio()


def token_coverage(hit_title, ref_string):
    """hit 标题的实词是否基本出现在整条引文串中（引文解析失败时的兜底判据）。"""
    tokens = [t for t in re.split(r"[\s\-–—.,;:()]+", (hit_title or "").lower()) if len(t) > 2]
    if not tokens:
        return 0.0
    low = norm_text(ref_string)
    hit = sum(1 for t in tokens if t in low)
    return hit / len(tokens)


# ---------------------------------------------------------------- 引文解析

BULLET_RE = re.compile(r"^\s*(?:\d{1,3}[.、)）]|[-*•]|\(?[a-zA-Z][).])\s+")
DOI_RE = re.compile(r"10\.\d{4,9}/[^\s,;，；>»\)\]】\"]+", re.I)
YEAR_RE = re.compile(r"(?:19|20)\d{2}")
POLICY_WORDS = ("通知", "意见", "条例", "办法", "纲要", "方案", "规划", "决定",
                "公报", "准则", "实施细则", "行动计划", "工作要点", "规定", "指南")
DOCNUM_RE = re.compile(r"[\u4e00-\u9fff]{2,20}〔?\[?(?:19|20)\d{2}\]?〕?\s*第?\d+\s*号")


def parse_refs(path):
    refs = []
    with open(path, encoding="utf-8-sig", errors="replace") as f:
        for raw in f:
            line = BULLET_RE.sub("", raw.strip())
            if not line:
                continue
            # 还原 Markdown 链接 [text](url) → text url，避免丢失链接里的 DOI
            line = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", r"\1 \2", line)
            refs.append(line)
    return refs


def is_chinese(s):
    return bool(re.search(r"[\u4e00-\u9fff]", s))


def is_policy(ref):
    if DOCNUM_RE.search(ref):
        return True
    if "《" in ref and any(w in ref for w in POLICY_WORDS):
        return True
    if any(w in ref for w in POLICY_WORDS) and re.search(r"(中共中央|国务院|教育部|中组部|中央宣传部|办公厅|省委|组织部|宣传部)", ref):
        return True
    return False


def extract_doi(ref):
    m = DOI_RE.search(ref)
    if not m:
        return None
    doi = m.group(0).rstrip(".,")
    # 修复含括号的 DOI（如 Elsevier 老格式 10.1016/S0140-6736(97)11096-0）：
    # 正则排除右括号导致截断时，向后补全直到括号闭合
    if doi.count("(") > doi.count(")"):
        tail = re.match(r"[^\s,;，；。、]*", ref[m.end():])
        if tail:
            doi = (doi + tail.group(0)).rstrip(".,")
    return doi


def extract_year(ref):
    years = YEAR_RE.findall(ref)
    return int(years[0]) if years else None


def extract_title(ref):
    """尽力而为地从引文串中抽取题目（GB/T 7714 或 APA 风格）。"""
    if is_chinese(ref):
        m = re.search(r"[.。]\s*([^.\[\]【】〔〕]{3,100}?)\s*[\[【]\s*(?:J|M|D|C|N|R|S|G|P|EB/?OL|A|Z)", ref)
        if m:
            return m.group(1).strip(" .,，。；;")
        m = re.search(r"《([^《》]{3,80})》", ref)
        if m:
            return m.group(1).strip()
        return None
    m = re.search(r"\((?:19|20)\d{2}[a-z]?\)\s*[.。]?\s*(.+)", ref)
    if m:
        seg = m.group(1)
        parts = re.split(r"\.\s+", seg, maxsplit=1)
        return parts[0].strip(" .,;") or None
    return None


def extract_first_author(ref):
    if is_chinese(ref):
        m = re.match(r"^([\u4e00-\u9fff]{2,4})", ref)
        return m.group(1) if m else None
    m = re.match(r"^([A-Z][A-Za-z'’\-]+)", ref)
    return m.group(1) if m else None


def extract_journal(ref):
    if is_chinese(ref):
        m = re.search(r"[\[【]\s*J\s*[\]】]\.?\s*([^,，.。;；]{2,60})", ref)
        return m.group(1).strip() if m else None
    # APA：题目之后、卷号之前的刊名段
    t = extract_title(ref)
    if t:
        idx = ref.find(t)
        if idx >= 0:
            rest = ref[idx + len(t):].lstrip(" .,;")
            # 刊名后紧跟卷号（可带逗号），卷号后接 "(" 或 ","——兼容两种 APA 卷期写法
            m = re.match(r"([A-Z][A-Za-z&\s\-]+?)[,\s]*\d{1,4}\s*[,(]", rest)
            if m:
                return m.group(1).strip()
            m = re.match(r"([A-Z][^.]{2,60})\.", rest)
            if m:
                j = m.group(1).strip()
                # 去掉误吞的尾部卷期页（如 "Nature, 521, 436-444" → "Nature"）
                m2 = re.match(r"^(.+?),?\s+\d{1,4}\b", j)
                if m2 and len(m2.group(1).strip(" ,")) >= 2:
                    return m2.group(1).strip(" ,")
                return j
    return None


# ---------------------------------------------------------------- Crossref 核验

def fetch_by_doi(doi):
    return http_get_json(f"{CROSSREF}/works/{urllib.parse.quote(doi)}")["message"]


def search_bibliographic(ref, rows=5):
    url = (f"{CROSSREF}/works?query.bibliographic="
           f"{urllib.parse.quote(ref)}&rows={rows}&select=DOI,title,author,container-title,issued")
    return http_get_json(url)["message"]["items"]


def cr_year(item):
    try:
        parts = item["issued"]["date-parts"][0]
        return parts[0] if parts else None
    except Exception:
        return None


def cr_first_author(item):
    try:
        a = item.get("author") or []
        fam = a[0].get("family") or a[0].get("name") or ""
        return fam or None
    except Exception:
        return None


def cr_journal(item):
    ct = item.get("container-title") or []
    return ct[0] if ct else None


def check_updates(item):
    """Gate D 出版诚信检查：Crossref update-to 字段（更正/撤稿声明）。

    返回 (说明文本, 是否撤稿)。撤稿 → 调用方按 CONFLICT 处理（默认排除）；
    更正 → 保持 VERIFIED 但附警告（建议核对/引用更正后版本）。
    """
    updates = item.get("update-to") or []
    if not updates:
        return "", False
    labels, retracted = [], False
    for u in updates:
        t = (u.get("type") or u.get("label") or "").lower()
        doi = u.get("DOI") or ""
        if "retract" in t:
            retracted = True
            labels.append(f"撤稿声明({doi})" if doi else "撤稿声明")
        else:
            labels.append(f"更正声明({doi})" if doi else "更正声明")
    return "存在后续" + "、".join(dict.fromkeys(labels)) + "，请核对最新版本", retracted


def compare_fields(ref, item):
    """返回 (冲突列表, 相似度)。item 为 Crossref 记录。"""
    conflicts = []
    claimed_title = extract_title(ref)
    hit_title = (item.get("title") or [""])[0]
    title_sim = sim(claimed_title, hit_title) if claimed_title else token_coverage(hit_title, ref)
    if claimed_title and title_sim < TITLE_SIM_PASS:
        conflicts.append(f"题目不匹配（相似度 {title_sim:.2f}）：引文「{claimed_title}」vs Crossref「{hit_title}」")
    if not claimed_title and token_coverage(hit_title, ref) < 0.80:
        conflicts.append(f"Crossref 题目「{hit_title}」的实词基本未出现在引文中（覆盖率 {token_coverage(hit_title, ref):.2f}）")

    y_claim, y_hit = extract_year(ref), cr_year(item)
    if y_claim and y_hit and abs(y_claim - y_hit) > YEAR_TOL:
        conflicts.append(f"年份不匹配：引文 {y_claim} vs Crossref {y_hit}")

    a_claim, a_hit = extract_first_author(ref), cr_first_author(item)
    if a_claim and a_hit and norm_text(a_claim) not in norm_text(a_hit) and norm_text(a_hit) not in norm_text(a_claim):
        conflicts.append(f"第一作者不匹配：引文「{a_claim}」vs Crossref「{a_hit}」")

    j_claim, j_hit = extract_journal(ref), cr_journal(item)
    if j_claim and j_hit and sim(j_claim, j_hit) < 0.70 and norm_text(j_claim) not in norm_text(j_hit):
        conflicts.append(f"期刊不匹配：引文「{j_claim}」vs Crossref「{j_hit}」")

    return conflicts, (title_sim if claimed_title else token_coverage(hit_title, ref))


def verify_one(ref):
    """核验单条文献，返回结果 dict。"""
    result = {"ref": ref, "status": "ERROR", "detail": "", "doi": extract_doi(ref)}

    if is_policy(ref):
        result["status"] = "POLICY"
        result["detail"] = "政策文件：请到发文机关官网（gov.cn / moe.gov.cn 等）逐字核对发文全称与文号"
        return result

    if is_chinese(ref):
        result["status"] = "CNKI_CHANNEL"
        result["detail"] = "中文文献：Crossref 覆盖有限，请到 CNKI/万方/维普人工核验题名、作者、刊名、年卷期页"
        return result

    # --- 有 DOI：直接取记录核验 ---
    if result["doi"]:
        try:
            item = fetch_by_doi(result["doi"])
            conflicts, tsim = compare_fields(ref, item)
            upd_note, is_retracted = check_updates(item)
            if conflicts:
                result["status"] = "CONFLICT"
                result["detail"] = "DOI 可解析但字段冲突：" + "；".join(conflicts)
            elif is_retracted:
                result["status"] = "CONFLICT"
                result["detail"] = f"出版诚信警告（Gate D）：该文献已被撤稿（{upd_note}）——默认排除，除非任务专门研究该撤稿事件"
            else:
                result["status"] = "VERIFIED"
                result["detail"] = f"五要素核验通过（DOI 直查，标题相似度 {tsim:.2f}）" + (f"；⚠️ {upd_note}" if upd_note else "")
            return result
        except urllib.error.HTTPError as e:
            if e.code == 404:
                if doi_resolves(result["doi"]):
                    result["status"] = "CNKI_CHANNEL"
                    result["detail"] = "DOI 在 Crossref 无记录但 doi.org 可解析（可能由中国 DOI/ISTIC 等机构注册），转人工通道核验"
                else:
                    result["status"] = "NOT_FOUND"
                    result["detail"] = f"DOI「{result['doi']}」不存在（Crossref 与 doi.org 均无法解析），高度疑似捏造"
            else:
                result["detail"] = f"Crossref 请求失败（HTTP {e.code}），转人工通道"
            return result
        except Exception as e:
            result["detail"] = f"网络异常：{type(e).__name__}，转人工通道（WebSearch）"
            return result

    # --- 无 DOI：书目检索 ---
    try:
        items = search_bibliographic(ref)
    except Exception as e:
        result["detail"] = f"Crossref 检索异常：{type(e).__name__}，转人工通道（WebSearch）"
        return result

    if not items:
        result["status"] = "NOT_FOUND"
        result["detail"] = "Crossref 无任何候选——英文文献视为存疑，按宁缺毋滥处理"
        return result

    best, best_conf, best_sim = None, None, -1.0
    for it in items:
        conf, s = compare_fields(ref, it)
        t_claim = extract_title(ref)
        if not t_claim:
            hit_t = (it.get("title") or [""])[0]
            s = token_coverage(hit_t, ref)
        if s > best_sim:
            best, best_conf, best_sim = it, conf, s

    if best_sim >= TITLE_SIM_PASS and not best_conf:
        upd_note, is_retracted = check_updates(best)
        if is_retracted:
            result["status"] = "CONFLICT"
            result["detail"] = f"出版诚信警告（Gate D）：该文献已被撤稿（{upd_note}）——默认排除，除非任务专门研究该撤稿事件"
            return result
        result["status"] = "VERIFIED"
        result["doi"] = best.get("DOI")
        result["detail"] = f"五要素核验通过（书目检索，标题相似度 {best_sim:.2f}），DOI：{best.get('DOI')}" + (f"；⚠️ {upd_note}" if upd_note else "")
    elif best_sim >= TITLE_SIM_WEAK:
        result["status"] = "CONFLICT"
        result["detail"] = (f"标题相似度不足（{best_sim:.2f}），疑似不匹配。候选："
                            f"「{(best.get('title') or [''])[0]}」（{best.get('DOI')}）。"
                            + ("其他冲突：" + "；".join(best_conf) if best_conf else ""))
    else:
        result["status"] = "NOT_FOUND"
        result["detail"] = f"最佳候选相似度仅 {best_sim:.2f}，无可靠匹配——视为存疑，按宁缺毋滥处理"
    return result


# ---------------------------------------------------------------- 正文↔列表对应核验

def check_body(body_path, refs):
    """尽力而为：编号引用 [n]/(n)/[n-m]/[n,m] 与 作者-年份 两种风格的对应检查。"""
    with open(body_path, encoding="utf-8-sig", errors="replace") as f:
        text = f.read()
    issues = []
    n = len(refs)
    cited = set()
    for m in re.finditer(r"[\[（(]\s*(\d{1,3}(?:\s*[-–,，、至]\s*\d{1,3})*)\s*[\]）)]", text):
        for part in re.split(r"[,，、]", m.group(1)):
            part = part.strip()
            if not part:
                continue
            rng = re.split(r"[-–至]", part)
            if len(rng) == 2 and rng[0].strip().isdigit() and rng[1].strip().isdigit():
                lo, hi = int(rng[0]), int(rng[1])
                if hi >= lo > 0 and hi - lo < 50:
                    cited.update(range(lo, hi + 1))
            elif part.isdigit():
                cited.add(int(part))
    out_of_range = sorted(c for c in cited if c > n)
    if out_of_range:
        issues.append(f"正文引用了编号 {out_of_range}，但参考文献列表只有 {n} 条——存在无对应文献的引用")
    never_cited = [i + 1 for i in range(n) if (i + 1) not in cited]
    # 作者-年份风格兜底：编号引用可能一个都没有
    if cited:
        if never_cited:
            issues.append(f"以下编号的文献在正文中未见编号引用，请确认是否漏引或改用了作者-年份格式：{never_cited}")
    else:
        for i, ref in enumerate(refs):
            a, y = extract_first_author(ref), extract_year(ref)
            if a and y and (a not in text):
                issues.append(f"第 {i + 1} 条文献的第一作者「{a}」未出现在正文中，疑似未被引用")
                continue
    return issues


# ---------------------------------------------------------------- 主流程

ICON = {"VERIFIED": "✅", "CONFLICT": "⚠️", "NOT_FOUND": "❌",
        "CNKI_CHANNEL": "🔎", "POLICY": "📜", "ERROR": "⚠️"}


def main():
    ap = argparse.ArgumentParser(description="参考文献防幻觉核验")
    ap.add_argument("refs_file", help="文献列表文件（每行一条）")
    ap.add_argument("--body", help="正文文件（核验正文引用与列表一一对应）")
    ap.add_argument("--report", help="输出 Markdown 核验报告的路径")
    args = ap.parse_args()

    refs = parse_refs(args.refs_file)
    if not refs:
        print("未解析到任何文献条目，请检查文件格式（每行一条）。")
        sys.exit(2)

    print(f"共解析 {len(refs)} 条文献，开始逐条核验（Crossref）…\n")
    results = []
    for i, ref in enumerate(refs, 1):
        r = verify_one(ref)
        r["no"] = i
        results.append(r)
        print(f"  [{i}/{len(refs)}] {ICON[r['status']]} {r['status']}: {ref[:60]}{'…' if len(ref) > 60 else ''}")
        time.sleep(REQUEST_INTERVAL)

    body_issues = []
    if args.body:
        body_issues = check_body(args.body, refs)

    # ---- Gate G：去重与版本控制 ----
    dup_issues = []
    seen_doi, seen_title = {}, {}
    for r in results:
        if r.get("doi"):
            k = r["doi"].lower()
            if k in seen_doi:
                dup_issues.append(f"第 {r['no']} 条与第 {seen_doi[k]} 条 DOI 相同（{r['doi']}）——同一文献重复计入，须合并（Gate G）")
            else:
                seen_doi[k] = r["no"]
        t = norm_text(extract_title(r["ref"]) or "")
        if len(t) > 10:
            if t in seen_title:
                dup_issues.append(f"第 {r['no']} 条与第 {seen_title[t]} 条题目相同——疑似同一文献重复，须合并（Gate G）")
            else:
                seen_title[t] = r["no"]

    # ---- 汇总 ----
    counts = {}
    for r in results:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    print("\n========== 核验汇总 ==========")
    for k in ("VERIFIED", "CONFLICT", "NOT_FOUND", "CNKI_CHANNEL", "POLICY", "ERROR"):
        if counts.get(k):
            print(f"  {ICON[k]} {k}: {counts[k]} 条")
    if body_issues:
        print("\n---------- 正文对应检查 ----------")
        for it in body_issues:
            print(f"  ⚠️ {it}")
    if dup_issues:
        print("\n---------- 去重检查（Gate G） ----------")
        for it in dup_issues:
            print(f"  ⚠️ {it}")
    print("\n须处理：CONFLICT（修正或删除）、NOT_FOUND（删除并以可核验文献替代）、重复条目（合并）。")
    print("人工通道：CNKI_CHANNEL / POLICY / ERROR 按各自提示核验后放行。")

    # ---- Markdown 报告 ----
    if args.report:
        with open(args.report, "w", encoding="utf-8") as f:
            f.write("# 参考文献防幻觉核验报告\n\n")
            f.write(f"- 核验条目：{len(refs)} 条\n")
            f.write(f"- 通过：{counts.get('VERIFIED', 0)}｜冲突：{counts.get('CONFLICT', 0)}｜"
                    f"未找到：{counts.get('NOT_FOUND', 0)}｜人工通道："
                    f"{counts.get('CNKI_CHANNEL', 0) + counts.get('POLICY', 0) + counts.get('ERROR', 0)}\n\n")
            f.write("| # | 状态 | 条目 | 核验结论 |\n|---|------|------|----------|\n")
            for r in results:
                ref_esc = r["ref"].replace("|", "\\|")[:120]
                det = r["detail"].replace("|", "\\|")
                f.write(f"| {r['no']} | {ICON[r['status']]} {r['status']} | {ref_esc} | {det} |\n")
            if args.body:
                f.write("\n## 正文引用对应检查\n\n")
                if body_issues:
                    for it in body_issues:
                        f.write(f"- ⚠️ {it}\n")
                else:
                    f.write("- ✅ 正文引用与参考文献列表一一对应，无漏引、无空引\n")
            if dup_issues:
                f.write("\n## 去重检查（Gate G）\n\n")
                for it in dup_issues:
                    f.write(f"- ⚠️ {it}\n")
        print(f"\n报告已写入：{args.report}")

    hard_fail = counts.get("CONFLICT", 0) + counts.get("NOT_FOUND", 0) + len(dup_issues)
    sys.exit(1 if hard_fail else 0)


if __name__ == "__main__":
    main()
