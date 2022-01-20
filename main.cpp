#include <iostream>
#include <string>
#include <fstream>
#include <sstream>
#include <vector>
#include <map>
#include <algorithm>

struct Step
{
    std::string clause;
    int parentA;
    int parentB;
};

std::vector<Step> kb;
std::map<std::string, int> redundancy;

void printKB()
{
    for (int i = 0; i < kb.size(); i++)
    {
        std::cout << i+1 << ". " << kb[i].clause << " {";
        if (kb[i].parentA > 0 && kb[i].parentB > 0) 
        {
            std::cout << kb[i].parentA << ", " << kb[i].parentB;
        }
        std::cout << "}" << std::endl;
    }
}

void output(bool valid)
{
    for (int i = 0; i < kb.size(); i++)
    {
        std::cout << i+1 << ". " << kb[i].clause << " {";
        if (kb[i].parentA > 0 && kb[i].parentB > 0) 
        {
            std::cout << kb[i].parentA << ", " << kb[i].parentB;
        }
        std::cout << "}" << std::endl;
    }
    valid ? std::cout << "Valid" : std::cout << "Fail";
}

size_t find(std::string clause, std::string literal)
{
    size_t pos = 0;
    pos = clause.find(literal);
    int next = pos;

    // cases:
    // A: pos == 0
    // B: !std::isspace(clause[pos+literal.length()]
    // C: pos >= clause.length() - literal.length()
    // D: !std::isspace(clause[pos-1])
    // (AB) + (CD) + (!A!CBD)

    bool resolved = false;
    while (!resolved)
    {
        if (pos == std::string::npos || next >= clause.length()) 
        {
            break;
        }
        else if (pos == 0 && pos >= clause.length() - literal.length())
        {
            resolved = true;
        }
        else if (pos == 0 && !std::isspace(clause[pos+literal.length()]))
        {
            pos = clause.find(literal, next+literal.length());
            next = pos;
        } 
        else if (pos >= clause.length() - literal.length() && !std::isspace(clause[pos-1]))
        {
            pos = clause.find(literal, next+literal.length());
            next = pos;
        } 
        else if (pos > 0 && pos < clause.length() - literal.length() && (!std::isspace(clause[pos+literal.length()]) || !std::isspace(clause[pos-1])))
        {
            pos = clause.find(literal, next+literal.length());
            next = pos;
        }
        else
        {
            resolved = true;
        }
    }

    return pos;
}

std::vector<std::string> strToArray(std::string clause)
{
    std::vector<std::string> output;
    std::istringstream iss(clause);
    std::string split = "";
    while (iss >> split)
    {
        output.push_back(split);
    }
    return output;
}

std::string arrayToStr(std::vector<std::string> clause)
{
    std::string output;
    for (int i = 0; i < clause.size(); i++)
    {
        output += clause[i] + " ";
    }
    output.pop_back();
    return output;
}

std::string getMappedClause(std::string clause)
{
    std::vector<std::string> convert = strToArray(clause);
    std::sort(convert.begin(), convert.end());
    std::string mappedClause = arrayToStr(convert);
    return mappedClause;
}

std::string removeRedundantLiterals(std::string clause)
{
    std::vector<std::string> check = strToArray(clause);
    if (check.size() < 2)
    {
        return arrayToStr(check);
    }

    std::vector<std::string>::iterator end = check.end();
    for (std::vector<std::string>::iterator it = check.begin(); it != end; ++it) {
        end = std::remove(it + 1, end, *it);
    }
 
    check.erase(end, check.end());

    return arrayToStr(check);
}

std::string negate(std::string clause)
{
    std::string output;
    std::istringstream iss(clause);
    std::string split = "";
    while (iss >> split)
    {
        if (split[0] == '~')
        {
            split = split.substr(1);
        }
        else
        {
            split = "~" + split;
        }
        output += split + " ";
    }
    output.pop_back();
    return output;
}

bool resolution()
{
    for (int i = 1; i < kb.size(); i++)
    {
        for (int j = 0; j < i; j++)
        {
            std::string newClause = kb[i].clause + " " + kb[j].clause;

            bool reduced = false;

            std::map<std::string, int> frequency;
            std::istringstream iss(newClause);
            std::string split = "";
            while (iss >> split)
            {
                std::string negation = negate(split);
                frequency[split]++;

                if (frequency[negation] > 0)
                {
                    if (!reduced)
                    {
                        reduced = true;
                        size_t pos;

                        pos = find(newClause, split);
                        if (pos != std::string::npos)
                        {
                            (pos == 0) ? newClause.erase(pos, split.length()+1) : newClause.erase(pos-1, split.length()+1);
                            frequency[split]--;
                        }
                        
                        pos = find(newClause, negation);
                        if (pos != std::string::npos)
                        {
                            (pos == 0) ? newClause.erase(pos, negation.length()+1) : newClause.erase(pos-1, negation.length()+1);
                            frequency[negation]--;
                        }
                    }
                    else
                    {
                        reduced = false;
                        break;
                    }
                }
            }

            if (reduced)
            {
                if (newClause.empty())
                {
                    Step step = {"Contradiction", i+1, j+1};
                    kb.push_back(step);
                    return true;
                }

                std::string clause = removeRedundantLiterals(newClause);
                std::string check = getMappedClause(clause);
                redundancy[check]++;

                if (redundancy[check] < 2)
                {
                    Step step = {clause, i+1, j+1};
                    kb.push_back(step);
                }
            }            
        }
    }
    
    return false;
}

int main(int argc, char **argv)
{
    std::string kbFile = argv[1];

    std::string prove;

    std::ifstream infile;
    std::string readline;

    infile.open(kbFile);
    if (infile.is_open())
    {
        while (getline(infile, readline))
        {
            Step step = {readline, 0, 0};
            kb.push_back(step);
            std::string mappedClause = getMappedClause(readline);
            redundancy[mappedClause]++;
        }

        prove = kb.back().clause;
        kb.pop_back();

        std::string mappedClause = getMappedClause(prove);
        redundancy[mappedClause]--;

        std::istringstream iss(prove);
        std::string split = "";
        while (iss >> split)
        {
            std::string clause = negate(split);
            Step step = {clause, 0, 0};
            kb.push_back(step);
            std::string mappedClause = getMappedClause(clause);
            redundancy[mappedClause]++;
        }
    }

    bool valid = false;
    valid = resolution();
    output(valid);

    return 0;
}