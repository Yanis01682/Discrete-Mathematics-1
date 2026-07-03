#include <vector>
#include <iostream>
#include <string>
#include <algorithm>
#include <set>
#include <bits/stdc++.h>

using namespace std;

// 定义命题表达式结构体,如P,非P
struct Proposition {
    string name;    // 命题名称
    bool neg;       // 是否否定
};

// 定义子句结构体,如P或非Q或R，但是此处字句结构体中只有谓词没有或
struct Clause {
    vector<Proposition> props;    // 命题表达式列表
};

// 解析单个命题表达式//函数//例如将~P解析成Proposition结构，name为P，neg为1
Proposition parseProposition(const string& propStr) {
    Proposition prop;
    if (propStr[0] == '~') {
        prop.neg = true;//被否定
        prop.name = propStr.substr(1);
    } else {
        prop.neg = false;
        prop.name = propStr;
    }
    return prop;
}

// 解析单个子句//注意输入时\vee应该输入为\\vee否则编译器会误以为转义字符
// 解析单个子句，支持蕴含和双蕴含
Clause parseClause(const string& clauseStr) {
    // 检查是否存在蕴含或双蕴含
    size_t impliesPos = clauseStr.find("->");
    size_t doubleImpliesPos = clauseStr.find("<->");

    if (impliesPos != string::npos) {
        // 处理蕴含
        string antecedentStr = clauseStr.substr(0, impliesPos);
        string consequentStr = clauseStr.substr(impliesPos + 2);

        // 解析前件和后件
        Clause antecedentClause = parseClause(antecedentStr);
        Clause consequentClause = parseClause(consequentStr);

        // 生成前件的否定
        Clause negAntecedentClause;
        for (const auto& prop : antecedentClause.props) {
            negAntecedentClause.props.push_back({ prop.name, !prop.neg });
        }

        // 生成 (¬A ∨ B) 形式的子句
        Clause implicationClause;
        implicationClause.props.insert(implicationClause.props.end(), negAntecedentClause.props.begin(), negAntecedentClause.props.end());
        implicationClause.props.insert(implicationClause.props.end(), consequentClause.props.begin(), consequentClause.props.end());

        return implicationClause;
    } else if (doubleImpliesPos != string::npos) {
        // 处理双蕴含
        string leftStr = clauseStr.substr(0, doubleImpliesPos);
        string rightStr = clauseStr.substr(doubleImpliesPos + 2);

        // 解析左部和右部
        Clause leftClause = parseClause(leftStr);
        Clause rightClause = parseClause(rightStr);

        // 生成 (¬A ∨ B) 和 (¬B ∨ A) 形式的子句
        Clause implicationClause1;
        Clause implicationClause2;

        // 生成 (¬A ∨ B)
        Clause negLeftClause;
        for (const auto& prop : leftClause.props) {
            negLeftClause.props.push_back({ prop.name, !prop.neg });
        }
        implicationClause1.props.insert(implicationClause1.props.end(), negLeftClause.props.begin(), negLeftClause.props.end());
        implicationClause1.props.insert(implicationClause1.props.end(), rightClause.props.begin(), rightClause.props.end());

        // 生成 (¬B ∨ A)
        Clause negRightClause;
        for (const auto& prop : rightClause.props) {
            negRightClause.props.push_back({ prop.name, !prop.neg });
        }
        implicationClause2.props.insert(implicationClause2.props.end(), negRightClause.props.begin(), negRightClause.props.end());
        implicationClause2.props.insert(implicationClause2.props.end(), leftClause.props.begin(), leftClause.props.end());

        // 返回两个子句的合取
        Clause combinedClause;
        combinedClause.props.insert(combinedClause.props.end(), implicationClause1.props.begin(), implicationClause1.props.end());
        combinedClause.props.insert(combinedClause.props.end(), implicationClause2.props.begin(), implicationClause2.props.end());

        return combinedClause;
    } else {
        // 如果没有找到蕴含或双蕴含，直接解析为普通子句
        Clause clause;
        size_t pos = 0;
        while (pos < clauseStr.length()) {
            size_t endPos = clauseStr.find("\\vee", pos);
            if (endPos == string::npos) {
                endPos = clauseStr.length();
            }
            string propStr = clauseStr.substr(pos, endPos - pos);
            clause.props.push_back(parseProposition(propStr));
            pos = endPos + 4;  // "\\vee" 的长度是 4
        }
        return clause;
    }
}

// 解析前件
vector<Clause> parseAntecedent(const string& antecedentStr) {
    vector<Clause> clauses;
    stringstream ss(antecedentStr);//stringstream 用于按指定分隔符（在这里是逗号）分割字符串。
    string clauseStr;
    while (getline(ss, clauseStr, ',')) {
        clauses.push_back(parseClause(clauseStr));
    }
    return clauses;
}

// 解析后件，并生成其否定形式
Clause parseConsequent(const string& consequentStr) {
    Clause consequentClause = parseClause(consequentStr);
    Clause negConsequentClause;
    for (const auto& prop : consequentClause.props) {
        negConsequentClause.props.push_back({ prop.name, !prop.neg });
    }
    return negConsequentClause;
}

// 判断两个命题表达式是否可以消去
bool canEliminate(Proposition p1, Proposition p2) {
    return p1.name == p2.name && p1.neg != p2.neg;
}

// 消去两个命题表达式，并返回新的子句，比如输入子句为 P ∨ Q ∨ ¬P，并且要消去 P 和 ¬P：
Clause eliminate(Proposition p1, Proposition p2, const Clause& clause) {
    Clause newClause;
    for (const auto& prop : clause.props) {
        if (!(prop.name == p1.name && prop.neg == p1.neg)) {
            newClause.props.push_back(prop);
        }
    }
    return newClause;
}

// 执行归结过程
bool resolution(vector<Clause>& clauses) {
    bool changed = true;
    while (changed) {
        changed = false;//在每次循环开始时，将 changed 重置为 false。
        set<Clause> newClauses;
        for (size_t i = 0; i < clauses.size(); ++i) {
            for (size_t j = i + 1; j < clauses.size(); ++j) {
                //使用两层嵌套的 for 循环，遍历所有可能的子句对 (clauses[i], clauses[j])
                for (const auto& p1 : clauses[i].props) {
                    for (const auto& p2 : clauses[j].props) {
                        //再次使用两层嵌套的 for 循环，遍历子句 clauses[i] 和 clauses[j] 中的所有命题表达式对 (p1, p2)

                        if (canEliminate(p1, p2)) {
                            Clause newClause = eliminate(p1, p2, clauses[i]);
                            newClause.props.insert(newClause.props.end(), clauses[j].props.begin(), clauses[j].props.end());
                            // 移除重复的命题
                            sort(newClause.props.begin(), newClause.props.end());
                            newClause.props.erase(unique(newClause.props.begin(), newClause.props.end()), newClause.props.end());

                            // 检查是否已经存在相同的子句
                            if (std::find(clauses.begin(), clauses.end(), newClause) == clauses.end()) {
                                newClauses.insert(newClause);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        clauses.insert(clauses.end(), newClauses.begin(), newClauses.end());
    }
    // 检查是否有空子句
    for (const auto& clause : clauses) {
        if (clause.props.empty()) {
            return true; // 发现空子句，表示前件能推出后件
        }
    }
    return false; // 没有发现空子句，表示前件不能推出后件
}

int main() {
    int numClauses;//前件有几个子句
    cin >> numClauses;
    cin.ignore();  // 忽略换行符

    string antecedentStr;
    getline(cin, antecedentStr);

    string consequentStr;
    getline(cin, consequentStr);

    // 解析前件和后件
    vector<Clause> antecedentClauses = parseAntecedent(antecedentStr);//clause类型数组
    Clause consequentClause = parseConsequent(consequentStr);

    // 将后件的否定加入前件
    Clause negConsequentClause;
    for (const auto& prop : consequentClause.props) {
        negConsequentClause.props.push_back({prop.name, !prop.neg});
    }
    antecedentClauses.push_back(negConsequentClause);

    // 执行归结推理
    bool isEntailed = resolution(antecedentClauses);

    // 输出结果
    if (isEntailed) {
        cout << "是" << endl;
    } else {
        cout << "否" << endl;
    }

    return 0;
}