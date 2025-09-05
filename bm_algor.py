def bad_character_table(pattern):
    """生成坏字符表"""
    table = {}
    m = len(pattern)
    for i in range(m):
        table[pattern[i]] = max(1, m - i - 1)
    return table

def good_suffix_table(pattern):
    """生成好后缀表"""
    m = len(pattern)
    f = [0] * (m + 1)
    s = [0] * (m + 1)

    # Step 1: Compute f and s
    i = m
    j = m + 1
    f[i] = j
    while i > 0:
        while j <= m and pattern[i - 1] != pattern[j - 1]:
            if s[j] == 0: 
                s[j] = j - i
            j = f[j]
        i -= 1
        j -= 1
        f[i] = j

    # Step 2: Process the suffixes
    j = f[0]
    for i in range(m + 1):
        if s[i] == 0: 
            s[i] = j
        if i == j: 
            j = f[j]

    return s

def boyer_moore(text, pattern):
    """Boyer-Moore 字符串匹配算法"""
    n = len(text)
    m = len(pattern)
    
    if m > n:
        return []

    bad_char = bad_character_table(pattern)
    good_suffix = good_suffix_table(pattern)

    matches = []
    i = 0  # text pointer
    while i <= n - m:
        j = m - 1
        while j >= 0 and pattern[j] == text[i + j]:
            j -= 1
        
        if j < 0:
            matches.append(i)
            i += good_suffix[0] if i + m < n else 1
        else:
            bad_shift = bad_char.get(text[i + j], m)
            good_shift = good_suffix[j + 1]
            i += max(bad_shift, good_shift)
    
    return matches

# 示例
text = "HERE IS A SIMPLE EXAMPLE"
pattern = "EXAMPLE"
print(boyer_moore(text, pattern))  # 输出: [16]
