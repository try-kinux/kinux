#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/mount.h>
#include <dirent.h>
#include <errno.h>
#include <libgen.h>
#include <archive.h>
#include <archive_entry.h>
#include <zstd.h>
#include <pthread.h>
#include <curl/curl.h>
#include <fcntl.h>
#include <time.h>
#include <signal.h>
#include <sys/file.h>
#include <semaphore.h>
#include <json-c/json.h>
#include <openssl/sha.h>
#include <sys/select.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sched.h>

#define MAX_LINE 32768
#define MAX_CMD 8192
#define MAX_PATH 2048
#define MAX_PACKAGES 50000
#define MAX_VERSIONS 500
#define MAX_REPOS 50
#define MAX_DEPENDENCIES 100
#define MAX_CONFLICTS 50
#define MAX_PROVIDES 50
#define LOCK_TIMEOUT 30
#define DOWNLOAD_RETRIES 3
#define MAX_PARALLEL 8
#define HASH_SIZE 65

typedef struct {
    char name[256];
    char version[64];
    int version_major;
    int version_minor;
    int version_patch;
    char version_suffix[64];
} Version;

typedef struct {
    char name[256];
    char version[64];
    char operator[4];
} Dependency;

typedef struct {
    char name[256];
    char version[64];
    char operator[4];
} Conflict;

typedef struct {
    char name[256];
    char version[64];
} Provides;

typedef struct {
    char name[256];
    char fetch[2048];
    char version[64];
    int version_major;
    int version_minor;
    int version_patch;
    char version_suffix[64];
    char instructions[MAX_CMD];
    int has_instructions;
    char versions_fetch[MAX_VERSIONS][2048];
    char versions_tag[MAX_VERSIONS][64];
    int versions_major[MAX_VERSIONS];
    int versions_minor[MAX_VERSIONS];
    int versions_patch[MAX_VERSIONS];
    char versions_suffix[MAX_VERSIONS][64];
    int version_count;
    char tar_files[1024];
    int is_tar;
    int is_installed;
    char installed_version[64];
    char store_hash[HASH_SIZE];
    char repo_name[256];
    int priority;
    char description[1024];
    char homepage[512];
    char license[128];
    char maintainer[256];
    long installed_size;
    long download_size;
    Dependency dependencies[MAX_DEPENDENCIES];
    int dependency_count;
    Conflict conflicts[MAX_CONFLICTS];
    int conflict_count;
    Provides provides[MAX_PROVIDES];
    int provides_count;
    char check_fetch[2048];
    int has_check;
    int is_essential;
    int is_meta;
} Package;

typedef struct {
    char name[256];
    char url[2048];
    char path[MAX_PATH];
    int priority;
    int enabled;
    char last_update[64];
    int signed_only;
    char keyring[512];
} Repository;

typedef struct {
    char name[256];
    char old_version[64];
    char new_version[64];
    int is_downgrade;
} UpdateInfo;

typedef struct {
    char url[2048];
    char output[MAX_PATH];
    int retries;
    int success;
    pthread_mutex_t *lock;
} DownloadJob;

typedef struct {
    Package *packages;
    int count;
    Repository *repos;
    int repo_count;
    pthread_mutex_t lock;
    char home_dir[MAX_PATH];
    char db_dir[MAX_PATH];
    char cache_dir[MAX_PATH];
    char store_dir[MAX_PATH];
    char profiles_dir[MAX_PATH];
    char current_profile[MAX_PATH];
    char lock_file[MAX_PATH];
    int lock_fd;
} PackageDB;

PackageDB global_db;
UpdateInfo available_updates[MAX_PACKAGES];
int update_count = 0;
sem_t parallel_sem;

static size_t min_size(size_t a, size_t b) {
    return (a < b) ? a : b;
}

void compute_hash(const char *input, char *output) {
    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256_CTX ctx;
    SHA256_Init(&ctx);
    SHA256_Update(&ctx, input, strlen(input));
    SHA256_Final(digest, &ctx);
    
    for (int i = 0; i < SHA256_DIGEST_LENGTH; i++) {
        sprintf(output + (i * 2), "%02x", digest[i]);
    }
    output[64] = 0;
}

void compute_file_hash(const char *filepath, char *output) {
    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256_CTX ctx;
    SHA256_Init(&ctx);
    
    FILE *fp = fopen(filepath, "rb");
    if (!fp) {
        output[0] = 0;
        return;
    }
    
    unsigned char buffer[8192];
    size_t bytes;
    while ((bytes = fread(buffer, 1, sizeof(buffer), fp)) > 0) {
        SHA256_Update(&ctx, buffer, bytes);
    }
    fclose(fp);
    
    SHA256_Final(digest, &ctx);
    for (int i = 0; i < SHA256_DIGEST_LENGTH; i++) {
        sprintf(output + (i * 2), "%02x", digest[i]);
    }
    output[64] = 0;
}

void parse_version(const char *version_str, int *major, int *minor, int *patch, char *suffix) {
    *major = 0;
    *minor = 0;
    *patch = 0;
    suffix[0] = 0;

    if (!version_str) return;

    const char *v = version_str;
    if (*v == 'v' || *v == 'V') v++;

    *major = atoi(v);
    while (*v && *v != '.' && *v != '-' && *v != '_') v++;
    if (*v == '.') { v++; *minor = atoi(v); }
    while (*v && *v != '.' && *v != '-' && *v != '_') v++;
    if (*v == '.') { v++; *patch = atoi(v); }
    while (*v && *v != '-' && *v != '_') v++;
    if (*v == '-' || *v == '_') { v++; strncpy(suffix, v, 63); suffix[63] = 0; }
}

int compare_versions(const char *v1, const char *v2) {
    int m1, m2, mi1, mi2, p1, p2;
    char s1[64] = "", s2[64] = "";

    parse_version(v1, &m1, &mi1, &p1, s1);
    parse_version(v2, &m2, &mi2, &p2, s2);

    if (m1 != m2) return m1 - m2;
    if (mi1 != mi2) return mi1 - mi2;
    if (p1 != p2) return p1 - p2;

    if (s1[0] == 0 && s2[0] == 0) return 0;
    if (s1[0] == 0) return 1;
    if (s2[0] == 0) return -1;

    if (strstr(s1, "alpha") && !strstr(s2, "alpha")) return -1;
    if (strstr(s2, "alpha") && !strstr(s1, "alpha")) return 1;
    if (strstr(s1, "beta") && !strstr(s2, "beta")) return -1;
    if (strstr(s2, "beta") && !strstr(s1, "beta")) return 1;
    if (strstr(s1, "rc") && !strstr(s2, "rc")) return -1;
    if (strstr(s2, "rc") && !strstr(s1, "rc")) return 1;

    return strcmp(s1, s2);
}

int version_satisfies(const char *installed, const char *operator, const char *required) {
    int cmp = compare_versions(installed, required);

    if (strcmp(operator, ">=") == 0) return cmp >= 0;
    if (strcmp(operator, "<=") == 0) return cmp <= 0;
    if (strcmp(operator, ">") == 0) return cmp > 0;
    if (strcmp(operator, "<") == 0) return cmp < 0;
    if (strcmp(operator, "==") == 0 || strcmp(operator, "=") == 0) return cmp == 0;
    if (strcmp(operator, "!=") == 0) return cmp != 0;
    if (strcmp(operator, "") == 0) return 1;

    return cmp >= 0;
}

void create_symlink_tree(const char *store_path, const char *profile_path) {
    DIR *dir = opendir(store_path);
    if (!dir) return;
    
    struct dirent *entry;
    while ((entry = readdir(dir)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) continue;
        if (strcmp(entry->d_name, ".bux-meta") == 0) continue;
        
        char src[MAX_PATH], dst[MAX_PATH];
        snprintf(src, sizeof(src), "%s/%s", store_path, entry->d_name);
        snprintf(dst, sizeof(dst), "%s/%s", profile_path, entry->d_name);
        
        struct stat st;
        if (lstat(src, &st) == 0) {
            if (S_ISDIR(st.st_mode)) {
                mkdir(dst, 0755);
                create_symlink_tree(src, dst);
            } else {
                unlink(dst);
                symlink(src, dst);
            }
        }
    }
    closedir(dir);
}

void remove_profile_links(const char *profile_path) {
    DIR *dir = opendir(profile_path);
    if (!dir) return;
    
    struct dirent *entry;
    while ((entry = readdir(dir)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) continue;
        
        char path[MAX_PATH];
        snprintf(path, sizeof(path), "%s/%s", profile_path, entry->d_name);
        
        struct stat st;
        if (lstat(path, &st) == 0) {
            if (S_ISDIR(st.st_mode) && !S_ISLNK(st.st_mode)) {
                remove_profile_links(path);
                rmdir(path);
            } else {
                unlink(path);
            }
        }
    }
    closedir(dir);
}

void init_db() {
    memset(&global_db, 0, sizeof(PackageDB));
    pthread_mutex_init(&global_db.lock, NULL);

    strcpy(global_db.home_dir, getenv("HOME"));
    snprintf(global_db.db_dir, sizeof(global_db.db_dir), "%s/.bux/db", global_db.home_dir);
    snprintf(global_db.cache_dir, sizeof(global_db.cache_dir), "%s/.bux/cache", global_db.home_dir);
    snprintf(global_db.store_dir, sizeof(global_db.store_dir), "%s/.bux/store", global_db.home_dir);
    snprintf(global_db.profiles_dir, sizeof(global_db.profiles_dir), "%s/.bux/profiles", global_db.home_dir);
    snprintf(global_db.current_profile, sizeof(global_db.current_profile), "%s/.bux/profiles/default", global_db.home_dir);
    snprintf(global_db.lock_file, sizeof(global_db.lock_file), "%s/.bux/lock", global_db.home_dir);

    char bux_dir[MAX_PATH];
    snprintf(bux_dir, sizeof(bux_dir), "%s/.bux", global_db.home_dir);
    mkdir(bux_dir, 0755);
    mkdir(global_db.db_dir, 0755);
    mkdir(global_db.cache_dir, 0755);
    mkdir(global_db.store_dir, 0755);
    mkdir(global_db.profiles_dir, 0755);
    mkdir(global_db.current_profile, 0755);

    char repos_dir[MAX_PATH];
    snprintf(repos_dir, sizeof(repos_dir), "%s/repos", global_db.db_dir);
    mkdir(repos_dir, 0755);

    char installed_dir[MAX_PATH];
    snprintf(installed_dir, sizeof(installed_dir), "%s/installed", global_db.db_dir);
    mkdir(installed_dir, 0755);

    sem_init(&parallel_sem, 0, MAX_PARALLEL);
}

int acquire_lock() {
    global_db.lock_fd = open(global_db.lock_file, O_CREAT | O_RDWR, 0644);
    if (global_db.lock_fd < 0) return -1;

    if (flock(global_db.lock_fd, LOCK_EX) != 0) {
        close(global_db.lock_fd);
        return -1;
    }
    return 0;
}

void release_lock() {
    if (global_db.lock_fd > 0) {
        flock(global_db.lock_fd, LOCK_UN);
        close(global_db.lock_fd);
        global_db.lock_fd = 0;
    }
}

size_t write_callback(void *ptr, size_t size, size_t nmemb, void *stream) {
    FILE *fp = (FILE *)stream;
    size_t total = size * nmemb;
    if (total == 0) return 0;
    return fwrite(ptr, size, nmemb, fp);
}

int download_file_with_retry(const char *url, const char *output_path, int retries) {
    for (int i = 0; i < retries; i++) {
        CURL *curl = curl_easy_init();
        if (!curl) continue;

        FILE *fp = fopen(output_path, "wb");
        if (!fp) {
            curl_easy_cleanup(curl);
            continue;
        }

        curl_easy_setopt(curl, CURLOPT_URL, url);
        curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, write_callback);
        curl_easy_setopt(curl, CURLOPT_WRITEDATA, fp);
        curl_easy_setopt(curl, CURLOPT_FOLLOWLOCATION, 1L);
        curl_easy_setopt(curl, CURLOPT_MAXREDIRS, 10);
        curl_easy_setopt(curl, CURLOPT_TCP_FASTOPEN, 1L);
        curl_easy_setopt(curl, CURLOPT_BUFFERSIZE, 131072L);
        curl_easy_setopt(curl, CURLOPT_TIMEOUT, 300L);
        curl_easy_setopt(curl, CURLOPT_LOW_SPEED_LIMIT, 1024L);
        curl_easy_setopt(curl, CURLOPT_LOW_SPEED_TIME, 30L);
        curl_easy_setopt(curl, CURLOPT_SSL_VERIFYPEER, 1L);
        curl_easy_setopt(curl, CURLOPT_SSL_VERIFYHOST, 2L);
        curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);

        CURLcode res = curl_easy_perform(curl);
        long http_code = 0;
        curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &http_code);

        fclose(fp);
        curl_easy_cleanup(curl);

        if (res == CURLE_OK && http_code >= 200 && http_code < 400) return 0;

        if (i < retries - 1) {
            struct timespec ts;
            ts.tv_sec = 1 << i;
            ts.tv_nsec = 0;
            nanosleep(&ts, NULL);
        }
    }
    return -1;
}

int download_file(const char *url, const char *output_path) {
    return download_file_with_retry(url, output_path, DOWNLOAD_RETRIES);
}

void extract_tar_zstd(const char *archive_path, const char *dest_dir) {
    struct archive *a = archive_read_new();
    archive_read_support_filter_zstd(a);
    archive_read_support_filter_gzip(a);
    archive_read_support_filter_bzip2(a);
    archive_read_support_filter_xz(a);
    archive_read_support_filter_lzma(a);
    archive_read_support_format_tar(a);
    archive_read_support_format_zip(a);

    if (archive_read_open_filename(a, archive_path, 10240) != ARCHIVE_OK) {
        fprintf(stderr, "Failed to open archive: %s\n", archive_path);
        archive_read_free(a);
        return;
    }

    mkdir(dest_dir, 0755);

    struct archive_entry *entry;
    int r;
    while ((r = archive_read_next_header(a, &entry)) == ARCHIVE_OK) {
        char full_path[MAX_PATH];
        snprintf(full_path, sizeof(full_path), "%s/%s", dest_dir, archive_entry_pathname(entry));

        mode_t mode = archive_entry_filetype(entry);
        if (mode == AE_IFDIR) {
            mkdir(full_path, 0755);
        } else if (mode == AE_IFREG) {
            char dir_path[MAX_PATH];
            strncpy(dir_path, full_path, sizeof(dir_path) - 1);
            dir_path[sizeof(dir_path) - 1] = 0;
            char *parent = dirname(dir_path);
            mkdir(parent, 0755);

            int fd = open(full_path, O_WRONLY | O_CREAT | O_TRUNC, archive_entry_perm(entry));
            if (fd >= 0) {
                const void *buff;
                size_t size;
                off_t offset;
                while (archive_read_data_block(a, &buff, &size, &offset) == ARCHIVE_OK) {
                    size_t written = 0;
                    while (written < size) {
                        ssize_t n = write(fd, (const char*)buff + written, size - written);
                        if (n <= 0) break;
                        written += n;
                    }
                }
                close(fd);
            }
        } else if (mode == AE_IFLNK) {
            char dir_path[MAX_PATH];
            strncpy(dir_path, full_path, sizeof(dir_path) - 1);
            dir_path[sizeof(dir_path) - 1] = 0;
            char *parent = dirname(dir_path);
            mkdir(parent, 0755);
            symlink(archive_entry_symlink(entry), full_path);
        }
    }
    archive_read_close(a);
    archive_read_free(a);
}

void save_installed_db() {
    char path[MAX_PATH];
    snprintf(path, sizeof(path), "%s/installed/packages.json", global_db.db_dir);

    json_object *jroot = json_object_new_object();
    json_object *jpackages = json_object_new_array();

    for (int i = 0; i < global_db.count; i++) {
        if (global_db.packages[i].is_installed) {
            json_object *jpkg = json_object_new_object();
            json_object_object_add(jpkg, "name", json_object_new_string(global_db.packages[i].name));
            json_object_object_add(jpkg, "version", json_object_new_string(global_db.packages[i].installed_version));
            json_object_object_add(jpkg, "repo", json_object_new_string(global_db.packages[i].repo_name));
            json_object_object_add(jpkg, "essential", json_object_new_boolean(global_db.packages[i].is_essential));
            json_object_object_add(jpkg, "store_hash", json_object_new_string(global_db.packages[i].store_hash));
            json_object_array_add(jpackages, jpkg);
        }
    }

    json_object_object_add(jroot, "packages", jpackages);
    json_object_to_file(path, jroot);
    json_object_put(jroot);
}

void load_installed_db() {
    char path[MAX_PATH];
    snprintf(path, sizeof(path), "%s/installed/packages.json", global_db.db_dir);

    json_object *jroot = json_object_from_file(path);
    if (!jroot) return;

    json_object *jpackages;
    if (json_object_object_get_ex(jroot, "packages", &jpackages)) {
        int len = json_object_array_length(jpackages);
        for (int i = 0; i < len; i++) {
            json_object *jpkg = json_object_array_get_idx(jpackages, i);
            json_object *jname, *jversion, *jrepo, *jessential, *jhash;

            if (json_object_object_get_ex(jpkg, "name", &jname)) {
                const char *name = json_object_get_string(jname);
                for (int j = 0; j < global_db.count; j++) {
                    if (strcmp(global_db.packages[j].name, name) == 0) {
                        global_db.packages[j].is_installed = 1;
                        if (json_object_object_get_ex(jpkg, "version", &jversion)) {
                            strncpy(global_db.packages[j].installed_version, json_object_get_string(jversion), 63);
                            global_db.packages[j].installed_version[63] = 0;
                        }
                        if (json_object_object_get_ex(jpkg, "essential", &jessential)) {
                            global_db.packages[j].is_essential = json_object_get_boolean(jessential);
                        }
                        if (json_object_object_get_ex(jpkg, "store_hash", &jhash)) {
                            strncpy(global_db.packages[j].store_hash, json_object_get_string(jhash), HASH_SIZE - 1);
                            global_db.packages[j].store_hash[HASH_SIZE - 1] = 0;
                        }
                        break;
                    }
                }
            }
        }
    }
    json_object_put(jroot);
}

void save_repo_db() {
    char path[MAX_PATH];
    snprintf(path, sizeof(path), "%s/repos/repositories.json", global_db.db_dir);

    json_object *jroot = json_object_new_object();
    json_object *jrepos = json_object_new_array();

    for (int i = 0; i < global_db.repo_count; i++) {
        json_object *jrepo = json_object_new_object();
        json_object_object_add(jrepo, "name", json_object_new_string(global_db.repos[i].name));
        json_object_object_add(jrepo, "url", json_object_new_string(global_db.repos[i].url));
        json_object_object_add(jrepo, "priority", json_object_new_int(global_db.repos[i].priority));
        json_object_object_add(jrepo, "enabled", json_object_new_boolean(global_db.repos[i].enabled));
        json_object_array_add(jrepos, jrepo);
    }

    json_object_object_add(jroot, "repositories", jrepos);
    json_object_to_file(path, jroot);
    json_object_put(jroot);
}

void load_repo_db() {
    char path[MAX_PATH];
    snprintf(path, sizeof(path), "%s/repos/repositories.json", global_db.db_dir);

    json_object *jroot = json_object_from_file(path);
    if (!jroot) return;

    json_object *jrepos;
    if (json_object_object_get_ex(jroot, "repositories", &jrepos)) {
        int len = json_object_array_length(jrepos);
        for (int i = 0; i < len && global_db.repo_count < MAX_REPOS; i++) {
            json_object *jrepo = json_object_array_get_idx(jrepos, i);
            json_object *jname, *jurl, *jpriority, *jenabled;

            if (json_object_object_get_ex(jrepo, "name", &jname) &&
                json_object_object_get_ex(jrepo, "url", &jurl)) {
                Repository *repo = &global_db.repos[global_db.repo_count++];
                memset(repo, 0, sizeof(Repository));
                strncpy(repo->name, json_object_get_string(jname), 255);
                repo->name[255] = 0;
                strncpy(repo->url, json_object_get_string(jurl), 2047);
                repo->url[2047] = 0;
                if (json_object_object_get_ex(jrepo, "priority", &jpriority))
                    repo->priority = json_object_get_int(jpriority);
                if (json_object_object_get_ex(jrepo, "enabled", &jenabled))
                    repo->enabled = json_object_get_boolean(jenabled);
                else
                    repo->enabled = 1;
            }
        }
    }
    json_object_put(jroot);
}

void parse_dependency(const char *dep_str, Dependency *dep) {
    memset(dep, 0, sizeof(Dependency));

    char clean[512];
    strncpy(clean, dep_str, 511);
    clean[511] = 0;

    char *space = clean;
    while (*space == ' ') space++;

    char version_str[64] = "";
    char op[4] = "";

    if (strstr(space, ">=")) {
        sscanf(space, "%255s >= %63s", dep->name, version_str);
        strncpy(op, ">=", 3);
    } else if (strstr(space, "<=")) {
        sscanf(space, "%255s <= %63s", dep->name, version_str);
        strncpy(op, "<=", 3);
    } else if (strstr(space, "!=")) {
        sscanf(space, "%255s != %63s", dep->name, version_str);
        strncpy(op, "!=", 3);
    } else if (strstr(space, "==")) {
        sscanf(space, "%255s == %63s", dep->name, version_str);
        strncpy(op, "==", 3);
    } else if (strchr(space, '>')) {
        sscanf(space, "%255s > %63s", dep->name, version_str);
        strncpy(op, ">", 3);
    } else if (strchr(space, '<')) {
        sscanf(space, "%255s < %63s", dep->name, version_str);
        strncpy(op, "<", 3);
    } else if (strchr(space, '=')) {
        sscanf(space, "%255s = %63s", dep->name, version_str);
        strncpy(op, "=", 3);
    } else {
        strncpy(dep->name, space, 255);
        dep->name[255] = 0;
        return;
    }

    strncpy(dep->operator, op, 3);
    dep->operator[3] = 0;
    strncpy(dep->version, version_str, 63);
    dep->version[63] = 0;
}

Package* find_package(const char *name) {
    int best_priority = -1;
    Package *best = NULL;

    for (int i = 0; i < global_db.count; i++) {
        if (strcmp(global_db.packages[i].name, name) == 0) {
            if (global_db.packages[i].priority > best_priority) {
                best_priority = global_db.packages[i].priority;
                best = &global_db.packages[i];
            }
        }
    }

    if (!best) {
        for (int i = 0; i < global_db.count; i++) {
            for (int j = 0; j < global_db.packages[i].provides_count; j++) {
                if (strcmp(global_db.packages[i].provides[j].name, name) == 0) {
                    if (global_db.packages[i].priority > best_priority) {
                        best_priority = global_db.packages[i].priority;
                        best = &global_db.packages[i];
                    }
                }
            }
        }
    }

    return best;
}

Package* find_package_exact(const char *name, const char *version) {
    for (int i = 0; i < global_db.count; i++) {
        if (strcmp(global_db.packages[i].name, name) == 0 &&
            strcmp(global_db.packages[i].version, version) == 0) {
            return &global_db.packages[i];
        }
    }
    return NULL;
}

int is_package_installed(const char *name) {
    for (int i = 0; i < global_db.count; i++) {
        if (strcmp(global_db.packages[i].name, name) == 0 && global_db.packages[i].is_installed) {
            return 1;
        }
    }
    return 0;
}

char* get_installed_version(const char *name) {
    for (int i = 0; i < global_db.count; i++) {
        if (strcmp(global_db.packages[i].name, name) == 0 && global_db.packages[i].is_installed) {
            return global_db.packages[i].installed_version;
        }
    }
    return NULL;
}

int check_dependencies(Package *pkg, char error[MAX_LINE], int ignore_installed) {
    for (int i = 0; i < pkg->dependency_count; i++) {
        Dependency *dep = &pkg->dependencies[i];
        Package *dep_pkg = find_package(dep->name);

        if (!dep_pkg) {
            snprintf(error, MAX_LINE, "Dependency '%s' not found", dep->name);
            return -1;
        }

        if (dep_pkg->is_installed && !ignore_installed) {
            if (dep->version[0] && !version_satisfies(dep_pkg->installed_version, dep->operator, dep->version)) {
                snprintf(error, MAX_LINE, "Dependency '%s' version mismatch: installed %s, required %s %s",
                        dep->name, dep_pkg->installed_version, dep->operator, dep->version);
                return -1;
            }
        }
    }

    for (int i = 0; i < pkg->conflict_count; i++) {
        Conflict *conf = &pkg->conflicts[i];
        Package *conf_pkg = find_package(conf->name);

        if (conf_pkg && conf_pkg->is_installed) {
            if (!conf->version[0] || version_satisfies(conf_pkg->installed_version, conf->operator, conf->version)) {
                snprintf(error, MAX_LINE, "Conflicts with installed package '%s'", conf->name);
                return -1;
            }
        }
    }

    return 0;
}

int resolve_dependencies_recursive(Package *pkg, Package **to_install, int *to_install_count, int max_count, int depth) {
    if (depth > 50) return -1;

    for (int i = 0; i < pkg->dependency_count; i++) {
        Dependency *dep = &pkg->dependencies[i];
        Package *dep_pkg = find_package(dep->name);

        if (!dep_pkg) return -1;

        if (dep_pkg->is_installed && dep->version[0] &&
            !version_satisfies(dep_pkg->installed_version, dep->operator, dep->version)) {
            dep_pkg = find_package_exact(dep->name, dep->version);
            if (!dep_pkg) return -1;
        }

        int already_queued = 0;
        for (int j = 0; j < *to_install_count; j++) {
            if (strcmp(to_install[j]->name, dep_pkg->name) == 0 &&
                strcmp(to_install[j]->version, dep_pkg->version) == 0) {
                already_queued = 1;
                break;
            }
        }

        if (!dep_pkg->is_installed && !already_queued) {
            if (*to_install_count >= max_count) return -1;
            to_install[*to_install_count] = dep_pkg;
            (*to_install_count)++;

            if (resolve_dependencies_recursive(dep_pkg, to_install, to_install_count, max_count, depth + 1) != 0) {
                return -1;
            }
        }
    }

    return 0;
}

int execute_command(const char *cmd) {
    pid_t pid = fork();
    if (pid == 0) {
        setsid();
        execl("/bin/sh", "sh", "-c", cmd, (char *)NULL);
        _exit(127);
    } else if (pid > 0) {
        int status;
        waitpid(pid, &status, 0);
        if (WIFEXITED(status)) return WEXITSTATUS(status);
        return -1;
    }
    return -1;
}

void execute_instructions(const char *instructions, const char *work_dir) {
    char *cmd_copy = strdup(instructions);
    char *save_cwd = getcwd(NULL, 0);

    if (work_dir) chdir(work_dir);

    char *cmd = strtok(cmd_copy, "\n");
    while (cmd) {
        while (*cmd == ' ' || *cmd == '\t') cmd++;
        if (strlen(cmd) > 0 && cmd[0] != '#') {
            printf("\033[36m→\033[0m %s\n", cmd);
            int ret = execute_command(cmd);
            if (ret != 0) {
                fprintf(stderr, "\033[31mCommand failed with code %d\033[0m\n", ret);
            }
        }
        cmd = strtok(NULL, "\n");
    }

    if (save_cwd) {
        chdir(save_cwd);
        free(save_cwd);
    }
    free(cmd_copy);
}

void* parallel_download(void *arg) {
    DownloadJob *job = (DownloadJob *)arg;

    sem_wait(&parallel_sem);
    job->success = download_file_with_retry(job->url, job->output, job->retries);
    sem_post(&parallel_sem);

    return NULL;
}

int parallel_download_batch(DownloadJob *jobs, int count) {
    pthread_t *threads = calloc(count, sizeof(pthread_t));
    if (!threads) return -1;

    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, 1048576);

    for (int i = 0; i < count; i++) {
        pthread_create(&threads[i], &attr, parallel_download, &jobs[i]);
    }

    for (int i = 0; i < count; i++) {
        pthread_join(threads[i], NULL);
    }

    pthread_attr_destroy(&attr);
    free(threads);

    for (int i = 0; i < count; i++) {
        if (!jobs[i].success) return -1;
    }

    return 0;
}

int install_package_internal(Package *pkg, const char *version) {
    char error[MAX_LINE];

    if (pkg->is_installed && !version) {
        printf("Package '%s' is already installed (version %s)\n", pkg->name, pkg->installed_version);
        return 0;
    }

    if (check_dependencies(pkg, error, 0) != 0) {
        fprintf(stderr, "Dependency error: %s\n", error);
        return -1;
    }

    const char *fetch_url = pkg->fetch;
    const char *target_version = pkg->version;

    if (version) {
        for (int i = 0; i < pkg->version_count; i++) {
            if (strcmp(pkg->versions_tag[i], version) == 0) {
                fetch_url = pkg->versions_fetch[i];
                target_version = pkg->versions_tag[i];
                break;
            }
        }
    }

    char hash_input[MAX_PATH * 2];
    snprintf(hash_input, sizeof(hash_input), "%s-%s-%s", pkg->name, target_version, pkg->repo_name);
    char store_hash[HASH_SIZE];
    compute_hash(hash_input, store_hash);
    
    char store_path[MAX_PATH];
    snprintf(store_path, sizeof(store_path), "%s/%s", global_db.store_dir, store_hash);
    
    if (access(store_path, F_OK) == 0) {
        printf("Package '%s' already exists in store\n", pkg->name);
    } else {
        mkdir(store_path, 0755);
        
        char download_path[MAX_PATH];
        snprintf(download_path, sizeof(download_path), "%s/download", store_path);

        printf("\033[34m⬇ Downloading\033[0m %s %s...\n", pkg->name, target_version);
        printf("   URL: %s\n", fetch_url);

        if (download_file(fetch_url, download_path) != 0) {
            fprintf(stderr, "\033[31mDownload failed for %s\033[0m\n", pkg->name);
            rmdir(store_path);
            return -1;
        }

        if (pkg->is_tar && pkg->tar_files[0]) {
            char extract_dir[MAX_PATH];
            snprintf(extract_dir, sizeof(extract_dir), "%s/extracted", store_path);
            mkdir(extract_dir, 0755);

            printf("\033[36m📦 Extracting\033[0m %s...\n", pkg->name);
            extract_tar_zstd(download_path, extract_dir);

            char *files_copy = strdup(pkg->tar_files);
            char *token = strtok(files_copy, " ");
            while (token) {
                char src[MAX_PATH], dst[MAX_PATH];
                snprintf(src, sizeof(src), "%s/%s", extract_dir, token);
                snprintf(dst, sizeof(dst), "%s/%s", store_path, basename(token));
                pid_t pid = fork();
                if (pid == 0) {
                    execl("/bin/cp", "cp", "-rf", src, dst, (char *)NULL);
                    _exit(1);
                } else if (pid > 0) {
                    waitpid(pid, NULL, 0);
                }
                token = strtok(NULL, " ");
            }
            free(files_copy);
            unlink(download_path);
        }

        if (pkg->has_instructions) {
            printf("\033[33m🔧 Installing\033[0m %s...\n", pkg->name);
            execute_instructions(pkg->instructions, store_path);
        }
        
        char store_meta[MAX_PATH];
        snprintf(store_meta, sizeof(store_meta), "%s/.bux-meta", store_path);
        FILE *meta = fopen(store_meta, "w");
        if (meta) {
            fprintf(meta, "name=%s\nversion=%s\nhash=%s\n", pkg->name, target_version, store_hash);
            fclose(meta);
        }
    }

    create_symlink_tree(store_path, global_db.current_profile);
    
    strncpy(pkg->store_hash, store_hash, HASH_SIZE - 1);
    pkg->store_hash[HASH_SIZE - 1] = 0;
    strncpy(pkg->installed_version, target_version, 63);
    pkg->installed_version[63] = 0;
    pkg->is_installed = 1;

    save_installed_db();

    printf("\033[32m✓ Successfully installed\033[0m %s %s (store: %s)\n", pkg->name, target_version, store_hash);
    return 0;
}

int install_package(const char *name, const char *version) {
    if (acquire_lock() != 0) {
        fprintf(stderr, "Could not acquire lock. Another bux process may be running.\n");
        return -1;
    }

    Package *pkg = find_package(name);
    if (!pkg) {
        fprintf(stderr, "Package '%s' not found in any repository\n", name);
        release_lock();
        return -1;
    }

    Package *to_install[MAX_DEPENDENCIES * 2];
    int to_install_count = 0;
    to_install[to_install_count++] = pkg;

    if (resolve_dependencies_recursive(pkg, to_install, &to_install_count, MAX_DEPENDENCIES * 2, 0) != 0) {
        fprintf(stderr, "Failed to resolve dependencies\n");
        release_lock();
        return -1;
    }

    printf("\n\033[1mPackages to install (%d):\033[0m\n", to_install_count);
    for (int i = 0; i < to_install_count; i++) {
        printf("  %s %s [%s]\n", to_install[i]->name, to_install[i]->version, to_install[i]->repo_name);
    }
    printf("\n");

    for (int i = 0; i < to_install_count; i++) {
        if (install_package_internal(to_install[i], version) != 0) {
            fprintf(stderr, "Failed to install %s\n", to_install[i]->name);
            release_lock();
            return -1;
        }
    }

    release_lock();
    return 0;
}

void remove_package(const char *name) {
    if (acquire_lock() != 0) {
        fprintf(stderr, "Could not acquire lock.\n");
        return;
    }

    Package *pkg = find_package(name);
    if (!pkg || !pkg->is_installed) {
        fprintf(stderr, "Package '%s' is not installed\n", name);
        release_lock();
        return;
    }

    if (pkg->is_essential) {
        fprintf(stderr, "Cannot remove essential package '%s'\n", name);
        release_lock();
        return;
    }

    printf("\033[33mRemoving\033[0m %s...\n", name);

    remove_profile_links(global_db.current_profile);

    for (int i = 0; i < global_db.count; i++) {
        if (global_db.packages[i].is_installed && strcmp(global_db.packages[i].name, name) != 0) {
            char other_store[MAX_PATH];
            snprintf(other_store, sizeof(other_store), "%s/%s", global_db.store_dir, global_db.packages[i].store_hash);
            create_symlink_tree(other_store, global_db.current_profile);
        }
    }

    int store_used = 0;
    for (int i = 0; i < global_db.count; i++) {
        if (global_db.packages[i].is_installed && 
            strcmp(global_db.packages[i].store_hash, pkg->store_hash) == 0 && 
            strcmp(global_db.packages[i].name, name) != 0) {
            store_used = 1;
            break;
        }
    }

    if (!store_used) {
        char store_path[MAX_PATH];
        snprintf(store_path, sizeof(store_path), "%s/%s", global_db.store_dir, pkg->store_hash);
        pid_t pid = fork();
        if (pid == 0) {
            execl("/bin/rm", "rm", "-rf", store_path, (char *)NULL);
            _exit(1);
        } else if (pid > 0) {
            waitpid(pid, NULL, 0);
        }
        printf("Store garbage collected: %s\n", pkg->store_hash);
    }

    pkg->is_installed = 0;
    pkg->installed_version[0] = 0;
    pkg->store_hash[0] = 0;

    save_installed_db();

    printf("\033[32m✓ Removed\033[0m %s\n", name);
    release_lock();
}

void check_updates() {
    update_count = 0;

    for (int i = 0; i < global_db.count; i++) {
        if (!global_db.packages[i].is_installed) continue;

        Package *pkg = &global_db.packages[i];
        Package *latest = find_package(pkg->name);

        if (!latest) continue;
        if (strcmp(pkg->repo_name, latest->repo_name) != 0) continue;

        int cmp = compare_versions(latest->version, pkg->installed_version);

        if (cmp > 0) {
            UpdateInfo *update = &available_updates[update_count++];
            strncpy(update->name, pkg->name, 255);
            update->name[255] = 0;
            strncpy(update->old_version, pkg->installed_version, 63);
            update->old_version[63] = 0;
            strncpy(update->new_version, latest->version, 63);
            update->new_version[63] = 0;
            update->is_downgrade = 0;
        }
    }

    for (int i = 0; i < update_count; i++) {
        int swapped = 0;
        for (int j = 0; j < update_count - i - 1; j++) {
            if (strcmp(available_updates[j].name, available_updates[j + 1].name) > 0) {
                UpdateInfo temp = available_updates[j];
                available_updates[j] = available_updates[j + 1];
                available_updates[j + 1] = temp;
                swapped = 1;
            }
        }
        if (!swapped) break;
    }
}

void list_updates() {
    check_updates();

    if (update_count == 0) {
        printf("\033[32mAll packages are up to date.\033[0m\n");
        return;
    }

    printf("\n\033[1mAvailable updates (%d):\033[0m\n", update_count);
    printf("%-30s %-20s → %-20s\n", "Package", "Current", "Latest");
    printf("%-30s %-20s   %-20s\n", "───────", "───────", "──────");

    for (int i = 0; i < update_count; i++) {
        printf("%-30s %-20s → \033[32m%-20s\033[0m\n",
               available_updates[i].name,
               available_updates[i].old_version,
               available_updates[i].new_version);
    }
}

void upgrade_all() {
    check_updates();

    if (update_count == 0) {
        printf("\033[32mAll packages are up to date.\033[0m\n");
        return;
    }

    printf("\n\033[1mUpgrading %d package(s):\033[0m\n", update_count);

    for (int i = 0; i < update_count; i++) {
        printf("\n\033[34mUpgrading %s from %s to %s\033[0m\n",
               available_updates[i].name,
               available_updates[i].old_version,
               available_updates[i].new_version);
        install_package(available_updates[i].name, available_updates[i].new_version);
    }

    printf("\n\033[32m✓ Upgrade complete\033[0m\n");
}

void upgrade_package(const char *name) {
    Package *pkg = find_package(name);
    if (!pkg) {
        fprintf(stderr, "Package '%s' not found\n", name);
        return;
    }

    if (!pkg->is_installed) {
        fprintf(stderr, "Package '%s' is not installed\n", name);
        return;
    }

    check_updates();

    for (int i = 0; i < update_count; i++) {
        if (strcmp(available_updates[i].name, name) == 0) {
            printf("\033[34mUpgrading %s from %s to %s\033[0m\n",
                   available_updates[i].name,
                   available_updates[i].old_version,
                   available_updates[i].new_version);
            install_package(name, available_updates[i].new_version);
            return;
        }
    }

    printf("\033[32m%s is already at the latest version (%s)\033[0m\n", name, pkg->installed_version);
}

void search_packages(const char *query) {
    int found = 0;

    printf("\n\033[1mSearch results for \"%s\":\033[0m\n", query);
    printf("%-30s %-20s %-20s %s\n", "Package", "Version", "Repository", "Status");
    printf("%-30s %-20s %-20s %s\n", "───────", "───────", "──────────", "──────");

    for (int i = 0; i < global_db.count; i++) {
        if (strstr(global_db.packages[i].name, query) ||
            (global_db.packages[i].description[0] && strstr(global_db.packages[i].description, query))) {
            char status[64] = "";
            if (global_db.packages[i].is_installed) {
                snprintf(status, sizeof(status), "[installed %s]", global_db.packages[i].installed_version);
            }
            printf("%-30s %-20s %-20s %s\n",
                   global_db.packages[i].name,
                   global_db.packages[i].version,
                   global_db.packages[i].repo_name,
                   status);
            found++;
        }
    }

    if (found == 0) {
        printf("  No packages found.\n");
    } else {
        printf("\n  %d package(s) found.\n", found);
    }
}

void show_package_info(const char *name) {
    Package *pkg = find_package(name);
    if (!pkg) {
        fprintf(stderr, "Package '%s' not found\n", name);
        return;
    }

    printf("\n\033[1mPackage: %s\033[0m\n", pkg->name);
    printf("  Version:      %s\n", pkg->version);
    printf("  Repository:   %s (priority: %d)\n", pkg->repo_name, pkg->priority);
    printf("  Status:       %s\n", pkg->is_installed ? "Installed" : "Not installed");

    if (pkg->is_installed) {
        printf("  Installed ver: %s\n", pkg->installed_version);
        printf("  Store hash:   %s\n", pkg->store_hash);
    }

    if (pkg->description[0]) printf("  Description:  %s\n", pkg->description);
    if (pkg->homepage[0]) printf("  Homepage:     %s\n", pkg->homepage);
    if (pkg->license[0]) printf("  License:      %s\n", pkg->license);
    if (pkg->maintainer[0]) printf("  Maintainer:   %s\n", pkg->maintainer);
    if (pkg->installed_size) printf("  Size:         %ld bytes\n", pkg->installed_size);
    if (pkg->is_essential) printf("  Essential:    yes\n");

    if (pkg->dependency_count > 0) {
        printf("  Dependencies:\n");
        for (int i = 0; i < pkg->dependency_count; i++) {
            printf("    - %s", pkg->dependencies[i].name);
            if (pkg->dependencies[i].version[0]) {
                printf(" (%s %s)", pkg->dependencies[i].operator, pkg->dependencies[i].version);
            }
            printf("\n");
        }
    }

    if (pkg->conflict_count > 0) {
        printf("  Conflicts:\n");
        for (int i = 0; i < pkg->conflict_count; i++) {
            printf("    - %s", pkg->conflicts[i].name);
            if (pkg->conflicts[i].version[0]) {
                printf(" (%s %s)", pkg->conflicts[i].operator, pkg->conflicts[i].version);
            }
            printf("\n");
        }
    }

    if (pkg->version_count > 0) {
        printf("  Available versions:\n");
        for (int i = 0; i < pkg->version_count; i++) {
            printf("    - %s\n", pkg->versions_tag[i]);
        }
    }

    printf("\n");
}

void list_installed() {
    int count = 0;

    printf("\n\033[1mInstalled packages:\033[0m\n");
    printf("%-30s %-20s %-20s %s\n", "Package", "Version", "Repository", "Store");
    printf("%-30s %-20s %-20s %s\n", "───────", "───────", "──────────", "─────");

    for (int i = 0; i < global_db.count; i++) {
        if (global_db.packages[i].is_installed) {
            printf("%-30s %-20s %-20s %s\n",
                   global_db.packages[i].name,
                   global_db.packages[i].installed_version,
                   global_db.packages[i].repo_name,
                   global_db.packages[i].store_hash);
            count++;
        }
    }

    printf("\n  %d package(s) installed.\n\n", count);
}

void add_repository(const char *name, const char *url, int priority) {
    if (global_db.repo_count >= MAX_REPOS) {
        fprintf(stderr, "Maximum repositories reached\n");
        return;
    }

    for (int i = 0; i < global_db.repo_count; i++) {
        if (strcmp(global_db.repos[i].name, name) == 0) {
            fprintf(stderr, "Repository '%s' already exists\n", name);
            return;
        }
    }

    Repository *repo = &global_db.repos[global_db.repo_count++];
    memset(repo, 0, sizeof(Repository));
    strncpy(repo->name, name, 255);
    repo->name[255] = 0;
    strncpy(repo->url, url, 2047);
    repo->url[2047] = 0;
    repo->priority = priority ? priority : 500;
    repo->enabled = 1;

    save_repo_db();
    printf("\033[32mRepository '%s' added\033[0m\n", name);
}

void remove_repository(const char *name) {
    int found = 0;
    for (int i = 0; i < global_db.repo_count; i++) {
        if (strcmp(global_db.repos[i].name, name) == 0) {
            for (int j = i; j < global_db.repo_count - 1; j++) {
                global_db.repos[j] = global_db.repos[j + 1];
            }
            global_db.repo_count--;
            found = 1;
            break;
        }
    }

    if (found) {
        save_repo_db();
        printf("\033[32mRepository '%s' removed\033[0m\n", name);
    } else {
        fprintf(stderr, "Repository '%s' not found\n", name);
    }
}

void enable_repository(const char *name, int enable) {
    for (int i = 0; i < global_db.repo_count; i++) {
        if (strcmp(global_db.repos[i].name, name) == 0) {
            global_db.repos[i].enabled = enable;
            save_repo_db();
            printf("Repository '%s' %s\n", name, enable ? "enabled" : "disabled");
            return;
        }
    }
    fprintf(stderr, "Repository '%s' not found\n", name);
}

void list_repositories() {
    printf("\n\033[1mRepositories:\033[0m\n");
    printf("%-20s %-6s %-8s %s\n", "Name", "Prio", "Status", "URL");
    printf("%-20s %-6s %-8s %s\n", "────", "────", "──────", "───");

    for (int i = 0; i < global_db.repo_count; i++) {
        printf("%-20s %-6d %-8s %s\n",
               global_db.repos[i].name,
               global_db.repos[i].priority,
               global_db.repos[i].enabled ? "enabled" : "disabled",
               global_db.repos[i].url);
    }
    printf("\n");
}

void parse_packages_file(const char *filepath, const char *repo_name, int priority) {
    FILE *fp = fopen(filepath, "r");
    if (!fp) return;

    char line[MAX_LINE];
    Package *current = NULL;
    int in_instructions = 0;
    int in_versions = 0;
    int in_dependencies = 0;
    int in_conflicts = 0;
    int in_provides = 0;

    while (fgets(line, sizeof(line), fp)) {
        line[strcspn(line, "\n")] = 0;
        line[strcspn(line, "\r")] = 0;

        if (strncmp(line, "start_", 6) == 0) {
            if (global_db.count >= MAX_PACKAGES) {
                fclose(fp);
                return;
            }
            current = &global_db.packages[global_db.count];
            memset(current, 0, sizeof(Package));
            sscanf(line, "start_%255s", current->name);
            current->priority = priority;
            strncpy(current->repo_name, repo_name, 255);
            current->repo_name[255] = 0;
            in_instructions = 0;
            in_versions = 0;
            in_dependencies = 0;
            in_conflicts = 0;
            in_provides = 0;
        } else if (strncmp(line, "end_", 4) == 0) {
            if (current) {
                parse_version(current->version, &current->version_major,
                             &current->version_minor, &current->version_patch,
                             current->version_suffix);

                for (int i = 0; i < current->version_count; i++) {
                    parse_version(current->versions_tag[i],
                                 &current->versions_major[i],
                                 &current->versions_minor[i],
                                 &current->versions_patch[i],
                                 current->versions_suffix[i]);
                }

                global_db.count++;
                current = NULL;
            }
        } else if (line[0] == '"' && current) {
            char name[256], fetch[2048];
            if (sscanf(line, "\"%255[^\"]\" fetch=%2047s", name, fetch) == 2) {
                strncpy(current->name, name, 255);
                current->name[255] = 0;
                strncpy(current->fetch, fetch, 2047);
                current->fetch[2047] = 0;
            } else if (sscanf(line, "\"%255[^\"]\" fetch=%2047[^\n]", name, fetch) == 2) {
                strncpy(current->name, name, 255);
                current->name[255] = 0;
                strncpy(current->fetch, fetch, 2047);
                current->fetch[2047] = 0;
            }
        } else if (strncmp(line, "version=", 8) == 0 && current) {
            strncpy(current->version, line + 8, 63);
            current->version[63] = 0;
        } else if (strncmp(line, "description=", 12) == 0 && current) {
            strncpy(current->description, line + 12, 1023);
            current->description[1023] = 0;
        } else if (strncmp(line, "homepage=", 9) == 0 && current) {
            strncpy(current->homepage, line + 9, 511);
            current->homepage[511] = 0;
        } else if (strncmp(line, "license=", 8) == 0 && current) {
            strncpy(current->license, line + 8, 127);
            current->license[127] = 0;
        } else if (strncmp(line, "maintainer=", 11) == 0 && current) {
            strncpy(current->maintainer, line + 11, 255);
            current->maintainer[255] = 0;
        } else if (strncmp(line, "essential=", 10) == 0 && current) {
            current->is_essential = (strcmp(line + 10, "yes") == 0 || strcmp(line + 10, "true") == 0);
        } else if (strncmp(line, "check=", 6) == 0 && current) {
            strncpy(current->check_fetch, line + 6, 2047);
            current->check_fetch[2047] = 0;
            current->has_check = 1;
        } else if (strcmp(line, "[instructions]") == 0 && current) {
            in_instructions = 1;
            in_versions = 0;
            in_dependencies = 0;
            in_conflicts = 0;
            in_provides = 0;
            current->has_instructions = 1;
            current->instructions[0] = 0;
        } else if (strcmp(line, "[versions]") == 0 && current) {
            in_instructions = 0;
            in_versions = 1;
            in_dependencies = 0;
            in_conflicts = 0;
            in_provides = 0;
            current->version_count = 0;
        } else if (strcmp(line, "[dependencies]") == 0 && current) {
            in_instructions = 0;
            in_versions = 0;
            in_dependencies = 1;
            in_conflicts = 0;
            in_provides = 0;
        } else if (strcmp(line, "[conflicts]") == 0 && current) {
            in_instructions = 0;
            in_versions = 0;
            in_dependencies = 0;
            in_conflicts = 1;
            in_provides = 0;
        } else if (strcmp(line, "[provides]") == 0 && current) {
            in_instructions = 0;
            in_versions = 0;
            in_dependencies = 0;
            in_conflicts = 0;
            in_provides = 1;
        } else if (strcmp(line, "[tar_files]") == 0 && current) {
            current->is_tar = 1;
        } else if (strncmp(line, "tar_files=", 10) == 0 && current) {
            strncpy(current->tar_files, line + 10, 1023);
            current->tar_files[1023] = 0;
            current->is_tar = 1;
        } else if (in_instructions && current) {
            size_t cur_len = strlen(current->instructions);
            size_t remain = sizeof(current->instructions) - cur_len;
            if (remain > 2) {
                if (cur_len > 0) {
                    strncat(current->instructions, "\n", remain - 1);
                    cur_len++;
                    remain--;
                }
                strncat(current->instructions, line, remain - 1);
            }
        } else if (in_versions && current && line[0]) {
            char tag[64], url[2048];
            if (sscanf(line, "%63s %2047s", tag, url) == 2) {
                if (current->version_count < MAX_VERSIONS) {
                    strncpy(current->versions_tag[current->version_count], tag, 63);
                    current->versions_tag[current->version_count][63] = 0;
                    strncpy(current->versions_fetch[current->version_count], url, 2047);
                    current->versions_fetch[current->version_count][2047] = 0;
                    current->version_count++;
                }
            }
        } else if (in_dependencies && current && line[0]) {
            if (current->dependency_count < MAX_DEPENDENCIES) {
                parse_dependency(line, &current->dependencies[current->dependency_count]);
                current->dependency_count++;
            }
        } else if (in_conflicts && current && line[0]) {
            if (current->conflict_count < MAX_CONFLICTS) {
                parse_dependency(line, (Dependency*)&current->conflicts[current->conflict_count]);
                current->conflict_count++;
            }
        } else if (in_provides && current && line[0]) {
            if (current->provides_count < MAX_PROVIDES) {
                sscanf(line, "%255s %63s", current->provides[current->provides_count].name,
                       current->provides[current->provides_count].version);
                current->provides_count++;
            }
        }
    }
    fclose(fp);
}

void update_repository(const char *repo_name) {
    Repository *repo = NULL;
    for (int i = 0; i < global_db.repo_count; i++) {
        if (strcmp(global_db.repos[i].name, repo_name) == 0) {
            repo = &global_db.repos[i];
            break;
        }
    }

    if (!repo) {
        fprintf(stderr, "Repository '%s' not found\n", repo_name);
        return;
    }

    if (!repo->enabled) {
        fprintf(stderr, "Repository '%s' is disabled\n", repo_name);
        return;
    }

    printf("\033[34mUpdating repository:\033[0m %s\n", repo_name);

    char url[MAX_PATH];
    char repo_file[MAX_PATH];
    snprintf(repo_file, sizeof(repo_file), "%s/repos/%s.txt", global_db.db_dir, repo_name);
    snprintf(url, sizeof(url), "%s/packages.txt", repo->url);

    char temp_file[MAX_PATH];
    snprintf(temp_file, sizeof(temp_file), "%s/repos/%s.tmp", global_db.db_dir, repo_name);

    if (download_file_with_retry(url, temp_file, 3) == 0) {
        rename(temp_file, repo_file);

        time_t now = time(NULL);
        struct tm *tm_info = localtime(&now);
        strftime(repo->last_update, sizeof(repo->last_update), "%Y-%m-%d %H:%M:%S", tm_info);

        parse_packages_file(repo_file, repo->name, repo->priority);

        printf("\033[32m✓ Repository '%s' updated\033[0m (%s)\n", repo_name, repo->last_update);
    } else {
        unlink(temp_file);
        fprintf(stderr, "\033[31mFailed to update repository '%s'\033[0m\n", repo_name);
    }

    save_repo_db();
}

void update_all_repositories() {
    if (global_db.repo_count == 0) {
        fprintf(stderr, "No repositories configured\n");
        return;
    }

    printf("\033[1mUpdating all repositories...\033[0m\n\n");

    global_db.count = 0;

    for (int i = 0; i < global_db.repo_count; i++) {
        if (global_db.repos[i].enabled) {
            update_repository(global_db.repos[i].name);
        }
    }

    load_installed_db();
    save_repo_db();

    printf("\n\033[32m✓ All repositories updated. %d packages available.\033[0m\n", global_db.count);
}

void clean_cache() {
    printf("\033[33mCleaning package cache...\033[0m\n");

    pid_t pid = fork();
    if (pid == 0) {
        execl("/bin/rm", "rm", "-rf", global_db.cache_dir, (char *)NULL);
        _exit(1);
    } else if (pid > 0) {
        waitpid(pid, NULL, 0);
    }

    mkdir(global_db.cache_dir, 0755);

    printf("\033[32m✓ Cache cleaned\033[0m\n");
}

void garbage_collect_store() {
    printf("\033[33mRunning store garbage collection...\033[0m\n");
    
    DIR *dir = opendir(global_db.store_dir);
    if (!dir) return;
    
    struct dirent *entry;
    int removed = 0;
    
    while ((entry = readdir(dir)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) continue;
        
        int used = 0;
        for (int i = 0; i < global_db.count; i++) {
            if (global_db.packages[i].is_installed && strcmp(global_db.packages[i].store_hash, entry->d_name) == 0) {
                used = 1;
                break;
            }
        }
        
        if (!used) {
            char store_path[MAX_PATH];
            snprintf(store_path, sizeof(store_path), "%s/%s", global_db.store_dir, entry->d_name);
            pid_t pid = fork();
            if (pid == 0) {
                execl("/bin/rm", "rm", "-rf", store_path, (char *)NULL);
                _exit(1);
            } else if (pid > 0) {
                waitpid(pid, NULL, 0);
            }
            removed++;
        }
    }
    closedir(dir);
    
    printf("\033[32m✓ Garbage collection complete. Removed %d unused store paths.\033[0m\n", removed);
}

void show_help() {
    printf("\n\033[1mBUX Package Manager (Nix-style Store)\033[0m\n\n");
    printf("Usage: bux <command> [arguments]\n\n");
    printf("\033[1mPackage Management:\033[0m\n");
    printf("  install, i <pkg> [version]    Install a package\n");
    printf("  remove, rm, r <pkg>           Remove a package\n");
    printf("  upgrade <pkg>                 Upgrade a specific package\n");
    printf("  upgrade-all, up               Upgrade all packages\n");
    printf("  search, se <query>            Search for packages\n");
    printf("  info, show <pkg>              Show package information\n");
    printf("  list-installed, li            List installed packages\n");
    printf("  list-updates, lu              List available updates\n");
    printf("  clean                         Clean package cache\n");
    printf("  gc                            Garbage collect store\n\n");
    printf("\033[1mRepository Management:\033[0m\n");
    printf("  repo-add <name> <url> [prio]  Add a repository\n");
    printf("  repo-remove, repo-rm <name>   Remove a repository\n");
    printf("  repo-enable <name>            Enable a repository\n");
    printf("  repo-disable <name>           Disable a repository\n");
    printf("  repo-list, rl                 List repositories\n");
    printf("  update                        Update all repositories\n");
    printf("  update-repo <name>            Update a specific repository\n\n");
    printf("\033[1mBuilt-in Tools:\033[0m\n");
    printf("  max <url1,url2,...>           Parallel downloader\n");
    printf("  dist <rootfs>                 Enter distribution chroot\n");
    printf("  sandbox                       Enter sandboxed shell\n");
    printf("  audi start <name> [--testing] Terminal manager\n\n");
}

void install_max() {
    printf("Max downloader installed. Usage: bux max <url1,url2,...>\n");
}

void run_max(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "Usage: bux max <url1,url2,...>\n");
        return;
    }

    char *urls = argv[2];
    char *urls_copy = strdup(urls);
    char *token = strtok(urls_copy, ",");

    DownloadJob jobs[100];
    int job_count = 0;

    while (token && job_count < 100) {
        while (*token == ' ') token++;
        snprintf(jobs[job_count].url, sizeof(jobs[job_count].url), "%s", token);
        snprintf(jobs[job_count].output, sizeof(jobs[job_count].output), "download_%d", job_count);
        jobs[job_count].retries = DOWNLOAD_RETRIES;
        jobs[job_count].success = 0;
        job_count++;
        token = strtok(NULL, ",");
    }

    printf("\033[34mDownloading %d file(s) in parallel (max %d concurrent)...\033[0m\n", job_count, MAX_PARALLEL);

    if (parallel_download_batch(jobs, job_count) == 0) {
        printf("\033[32m✓ All downloads completed\033[0m\n");
    } else {
        fprintf(stderr, "\033[31mSome downloads failed\033[0m\n");
    }

    free(urls_copy);
}

void install_dist() {
    printf("Distribution chroot tool installed. Usage: bux dist <rootfs_path>\n");
}

void run_dist(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "Usage: bux dist <rootfs_path>\n");
        return;
    }

    char *target = argv[2];

    if (access(target, F_OK) != 0) {
        fprintf(stderr, "Rootfs path does not exist: %s\n", target);
        return;
    }

    char distro_type[64] = "alpine";
    char *target_basename = basename(target);

    if (strstr(target_basename, "ubuntu") || strstr(target_basename, "debian")) {
        strncpy(distro_type, "debian", 63);
        distro_type[63] = 0;
    } else if (strstr(target_basename, "arch")) {
        strncpy(distro_type, "arch", 63);
        distro_type[63] = 0;
    } else if (strstr(target_basename, "void")) {
        strncpy(distro_type, "void", 63);
        distro_type[63] = 0;
    } else if (strstr(target_basename, "alpine")) {
        strncpy(distro_type, "alpine", 63);
        distro_type[63] = 0;
    }

    printf("\033[34mEntering %s chroot at %s\033[0m\n", distro_type, target);

    pid_t pid;

    pid = fork();
    if (pid == 0) {
        execl("/bin/mount", "mount", "-t", "proc", "proc", NULL);
        _exit(1);
    } else if (pid > 0) waitpid(pid, NULL, 0);

    pid = fork();
    if (pid == 0) {
        execl("/bin/mount", "mount", "-t", "sysfs", "sys", NULL);
        _exit(1);
    } else if (pid > 0) waitpid(pid, NULL, 0);

    pid = fork();
    if (pid == 0) {
        execl("/bin/mount", "mount", "-o", "bind", "/dev", NULL);
        _exit(1);
    } else if (pid > 0) waitpid(pid, NULL, 0);

    pid = fork();
    if (pid == 0) {
        execl("/bin/mount", "mount", "-o", "bind", "/dev/pts", NULL);
        _exit(1);
    } else if (pid > 0) waitpid(pid, NULL, 0);

    pid = fork();
    if (pid == 0) {
        execl("/bin/cp", "cp", "/etc/resolv.conf", NULL);
        _exit(1);
    } else if (pid > 0) waitpid(pid, NULL, 0);

    char shell[64] = "/bin/bash";
    if (strcmp(distro_type, "alpine") == 0) strncpy(shell, "/bin/ash", 63);

    pid = fork();
    if (pid == 0) {
        execl("/usr/sbin/chroot", "chroot", target, shell, (char *)NULL);
        execl("/sbin/chroot", "chroot", target, shell, (char *)NULL);
        _exit(1);
    } else if (pid > 0) {
        waitpid(pid, NULL, 0);
    }

    pid = fork();
    if (pid == 0) {
        execl("/bin/umount", "umount", NULL);
        _exit(1);
    } else if (pid > 0) waitpid(pid, NULL, 0);

    pid = fork();
    if (pid == 0) {
        execl("/bin/umount", "umount", NULL);
        _exit(1);
    } else if (pid > 0) waitpid(pid, NULL, 0);

    pid = fork();
    if (pid == 0) {
        execl("/bin/umount", "umount", NULL);
        _exit(1);
    } else if (pid > 0) waitpid(pid, NULL, 0);

    pid = fork();
    if (pid == 0) {
        execl("/bin/umount", "umount", NULL);
        _exit(1);
    } else if (pid > 0) waitpid(pid, NULL, 0);

    printf("\033[32mExited chroot\033[0m\n");
}

void install_sandbox() {
    printf("Sandbox installed. Usage: bux sandbox\n");
}

void run_sandbox() {
    char sandbox_dir[MAX_PATH];
    snprintf(sandbox_dir, sizeof(sandbox_dir), "/tmp/bux_sandbox_%d", getpid());
    mkdir(sandbox_dir, 0755);

    printf("\033[34mEntering sandbox at %s\033[0m\n", sandbox_dir);

    pid_t pid = fork();
    if (pid == 0) {
        if (chroot(sandbox_dir) != 0) _exit(1);
        chdir("/");
        mkdir("/tmp", 0755);
        execl("/bin/sh", "/bin/sh", NULL);
        _exit(1);
    } else if (pid > 0) {
        int status;
        waitpid(pid, &status, 0);
    }

    pid = fork();
    if (pid == 0) {
        execl("/bin/rm", "rm", "-rf", sandbox_dir, (char *)NULL);
        _exit(1);
    } else if (pid > 0) {
        waitpid(pid, NULL, 0);
    }

    printf("\033[32mExited sandbox\033[0m\n");
}

void install_audi() {
    printf("Audi terminal manager installed. Usage: bux audi start <name> [--testing]\n");
}

void run_audi(int argc, char **argv) {
    if (argc < 4 || strcmp(argv[2], "start") != 0) {
        fprintf(stderr, "Usage: bux audi start <terminal_name> [--testing]\n");
        return;
    }

    char *term_name = argv[3];
    int testing = (argc >= 5 && strcmp(argv[4], "--testing") == 0);

    char term_dir[MAX_PATH];
    snprintf(term_dir, sizeof(term_dir), "/tmp/audi_%s", term_name);
    mkdir(term_dir, 0755);

    if (testing) {
        printf("\033[34mStarting Docker-based testing terminal: %s\033[0m\n", term_name);
        pid_t pid = fork();
        if (pid == 0) {
            execlp("docker", "docker", "run", "-it", "--name", NULL);
            _exit(1);
        } else if (pid > 0) {
            waitpid(pid, NULL, 0);
        }
    } else {
        printf("\033[34mStarting isolated terminal: %s\033[0m\n", term_name);

        pid_t pid = fork();
        if (pid == 0) {
            mkdir(term_dir, 0755);
            if (chroot(term_dir) != 0) _exit(1);
            chdir("/");
            mkdir("/tmp", 0755);
            mkdir("/dev", 0755);
            mkdir("/proc", 0755);
            mkdir("/sys", 0755);
            mount("proc", "/proc", "proc", 0, NULL);
            mount("sysfs", "/sys", "sysfs", 0, NULL);
            execl("/bin/sh", "/bin/sh", NULL);
            _exit(1);
        } else if (pid > 0) {
            int status;
            waitpid(pid, &status, 0);
        }
    }

    printf("\033[32mTerminal closed\033[0m\n");
}

int main(int argc, char **argv) {
    if (argc < 2) {
        show_help();
        return 1;
    }

    struct rlimit rlim;
    rlim.rlim_cur = 65536;
    rlim.rlim_max = 65536;
    setrlimit(RLIMIT_NOFILE, &rlim);

    signal(SIGPIPE, SIG_IGN);
    signal(SIGCHLD, SIG_DFL);

    init_db();
    load_repo_db();

    for (int i = 0; i < global_db.repo_count; i++) {
        if (global_db.repos[i].enabled) {
            char repo_file[MAX_PATH];
            snprintf(repo_file, sizeof(repo_file), "%s/repos/%s.txt", global_db.db_dir, global_db.repos[i].name);
            if (access(repo_file, F_OK) == 0) {
                parse_packages_file(repo_file, global_db.repos[i].name, global_db.repos[i].priority);
            }
        }
    }

    load_installed_db();

    if (strcmp(argv[1], "help") == 0 || strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "--help") == 0) {
        show_help();
    } else if (strcmp(argv[1], "install") == 0 || strcmp(argv[1], "i") == 0) {
        if (argc < 3) { fprintf(stderr, "Package name required\n"); return 1; }
        if (strcmp(argv[2], "max") == 0) install_max();
        else if (strcmp(argv[2], "dist") == 0) install_dist();
        else if (strcmp(argv[2], "sandbox") == 0) install_sandbox();
        else if (strcmp(argv[2], "audi") == 0) install_audi();
        else install_package(argv[2], argc >= 4 ? argv[3] : NULL);
    } else if (strcmp(argv[1], "remove") == 0 || strcmp(argv[1], "rm") == 0 || strcmp(argv[1], "r") == 0) {
        if (argc < 3) { fprintf(stderr, "Package name required\n"); return 1; }
        remove_package(argv[2]);
    } else if (strcmp(argv[1], "upgrade") == 0 || strcmp(argv[1], "up") == 0) {
        if (argc < 3) { fprintf(stderr, "Package name required\n"); return 1; }
        upgrade_package(argv[2]);
    } else if (strcmp(argv[1], "upgrade-all") == 0 || strcmp(argv[1], "full-upgrade") == 0) {
        upgrade_all();
    } else if (strcmp(argv[1], "search") == 0 || strcmp(argv[1], "se") == 0) {
        if (argc < 3) { fprintf(stderr, "Search query required\n"); return 1; }
        search_packages(argv[2]);
    } else if (strcmp(argv[1], "info") == 0 || strcmp(argv[1], "show") == 0) {
        if (argc < 3) { fprintf(stderr, "Package name required\n"); return 1; }
        show_package_info(argv[2]);
    } else if (strcmp(argv[1], "list-installed") == 0 || strcmp(argv[1], "li") == 0) {
        list_installed();
    } else if (strcmp(argv[1], "list-updates") == 0 || strcmp(argv[1], "lu") == 0) {
        list_updates();
    } else if (strcmp(argv[1], "clean") == 0) {
        clean_cache();
    } else if (strcmp(argv[1], "gc") == 0) {
        garbage_collect_store();
    } else if (strcmp(argv[1], "update") == 0) {
        update_all_repositories();
    } else if (strcmp(argv[1], "update-repo") == 0) {
        if (argc < 3) { fprintf(stderr, "Repository name required\n"); return 1; }
        update_repository(argv[2]);
    } else if (strcmp(argv[1], "repo-add") == 0) {
        if (argc < 4) { fprintf(stderr, "Usage: bux repo-add <name> <url> [priority]\n"); return 1; }
        add_repository(argv[2], argv[3], argc >= 5 ? atoi(argv[4]) : 500);
    } else if (strcmp(argv[1], "repo-remove") == 0 || strcmp(argv[1], "repo-rm") == 0) {
        if (argc < 3) { fprintf(stderr, "Repository name required\n"); return 1; }
        remove_repository(argv[2]);
    } else if (strcmp(argv[1], "repo-enable") == 0) {
        if (argc < 3) { fprintf(stderr, "Repository name required\n"); return 1; }
        enable_repository(argv[2], 1);
    } else if (strcmp(argv[1], "repo-disable") == 0) {
        if (argc < 3) { fprintf(stderr, "Repository name required\n"); return 1; }
        enable_repository(argv[2], 0);
    } else if (strcmp(argv[1], "repo-list") == 0 || strcmp(argv[1], "rl") == 0) {
        list_repositories();
    } else if (strcmp(argv[1], "max") == 0) {
        run_max(argc, argv);
    } else if (strcmp(argv[1], "dist") == 0) {
        run_dist(argc, argv);
    } else if (strcmp(argv[1], "sandbox") == 0) {
        run_sandbox();
    } else if (strcmp(argv[1], "audi") == 0) {
        run_audi(argc, argv);
    } else {
        fprintf(stderr, "Unknown command: %s\n", argv[1]);
        fprintf(stderr, "Run 'bux help' for usage information\n");
        return 1;
    }

    save_installed_db();
    save_repo_db();
    pthread_mutex_destroy(&global_db.lock);
    sem_destroy(&parallel_sem);

    return 0;
}
