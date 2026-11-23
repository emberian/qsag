// Copy-on-write fork at the first bus read of each mutated SRAM word. Each
// child inherits the literal RTL state of the unmutated prefix and executes
// every remaining clock, including the public status read.
#include <array>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <set>
#include <string>
#include <vector>
#include <sys/wait.h>
#include <unistd.h>
namespace {
std::array<std::vector<int>, 65536> by_word;
std::array<bool, 65536> visited{};
size_t planned, started, passed, running, limit;
bool child;
void reap() {
    int status = 0;
    if (wait(&status) < 0)
        std::abort();
    --running;
    if (WIFEXITED(status) && WEXITSTATUS(status) == 0)
        ++passed;
}
} // namespace
extern "C" int d1_begin(const char *path, int nworkers, int length) {
    std::ifstream in(path);
    std::set<int> unique;
    int offset, bit;
    std::string field;
    while (in >> offset >> bit >> field) {
        if (offset < 0 || offset >= length || bit < 0 || bit > 7)
            std::abort();
        int id = offset * 8 + bit;
        if (!unique.insert(id).second)
            std::abort();
        by_word.at(offset / 8).push_back(id);
    }
    if (!in.eof() || unique.empty() || nworkers < 1)
        std::abort();
    planned = unique.size();
    limit = nworkers;
    return int(planned);
}
extern "C" int d1_probe(int word) {
    if (child || word < 0 || visited.at(word))
        return -1;
    visited[word] = true;
    for (int id : by_word[word]) {
        while (running >= limit)
            reap();
        std::fflush(nullptr);
        pid_t pid = fork();
        if (pid < 0)
            std::abort();
        if (!pid) {
            child = true;
            return id;
        }
        ++running;
        ++started;
    }
    return -1;
}
extern "C" int d1_finish(int good) {
    std::fflush(nullptr);
    if (child)
        _exit(good ? 0 : 1);
    while (running)
        reap();
    std::printf("RTL mutation campaign rejected=%zu launched=%zu planned=%zu\n", passed, started,
                planned);
    return good && passed == planned && started == planned;
}
