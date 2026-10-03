#pragma once

#include <algorithm>
#include <cerrno>
#include <chrono>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <stdexcept>
#include <string>
#include <system_error>
#include <thread>
#include <utility>
#include <nlohmann/json.hpp>
#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#endif

namespace fan_io {
namespace fs = std::filesystem;
inline constexpr const char* revision = "windows-io-fix-1";

inline std::string display_path(const fs::path& path) {
    std::error_code ec;
    auto absolute = fs::absolute(path, ec);
    return (ec ? path : absolute.lexically_normal()).u8string();
}

#ifdef _WIN32
inline std::string windows_error(DWORD code) {
    const char* name = "WINDOWS_ERROR";
    switch (code) {
        case ERROR_ACCESS_DENIED: name = "ERROR_ACCESS_DENIED"; break;
        case ERROR_SHARING_VIOLATION: name = "ERROR_SHARING_VIOLATION"; break;
        case ERROR_LOCK_VIOLATION: name = "ERROR_LOCK_VIOLATION"; break;
        case ERROR_USER_MAPPED_FILE: name = "ERROR_USER_MAPPED_FILE"; break;
        case ERROR_FILE_NOT_FOUND: name = "ERROR_FILE_NOT_FOUND"; break;
        case ERROR_PATH_NOT_FOUND: name = "ERROR_PATH_NOT_FOUND"; break;
        case ERROR_DISK_FULL: name = "ERROR_DISK_FULL"; break;
    }
    std::string result = "Win32 error " + std::to_string(code) + " (" + name + ")";
    wchar_t message[1024];
    DWORD length = FormatMessageW(FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS,
        nullptr, code, 0, message, 1024, nullptr);
    while (length && (message[length - 1] == L'\r' || message[length - 1] == L'\n' || message[length - 1] == L' ')) --length;
    if (length) {
        const int size = WideCharToMultiByte(CP_UTF8, 0, message, int(length), nullptr, 0, nullptr, nullptr);
        if (size > 0) {
            std::string utf8(size, '\0');
            WideCharToMultiByte(CP_UTF8, 0, message, int(length), &utf8[0], size, nullptr, nullptr);
            result += ": " + utf8;
        }
    }
    return result;
}

inline bool retryable_replace_error(DWORD code) {
    return code == ERROR_ACCESS_DENIED || code == ERROR_SHARING_VIOLATION ||
        code == ERROR_LOCK_VIOLATION || code == ERROR_USER_MAPPED_FILE;
}
#endif

inline std::string filesystem_error(const std::error_code& ec) {
#ifdef _WIN32
    if (ec.category() == std::system_category()) return windows_error(DWORD(ec.value()));
#endif
    return std::string(ec.category().name()) + " error " + std::to_string(ec.value()) + ": " + ec.message();
}

inline std::runtime_error stream_error(const char* operation, const fs::path& path, int code) {
    return std::runtime_error(std::string(operation) + " " + display_path(path) +
        (code ? "; " + filesystem_error(std::error_code(code, std::generic_category())) : "; output stream failure"));
}

inline void atomic_json(const fs::path& path, const nlohmann::json& value) {
    if (!path.parent_path().empty()) {
        std::error_code ec;
        fs::create_directories(path.parent_path(), ec);
        if (ec) throw std::runtime_error("Cannot create output directory " + display_path(path.parent_path()) + "; " + filesystem_error(ec));
    }
    // Serialize first. An encoding error must not truncate a saved temporary file.
    const std::string payload = value.dump(2) + '\n';
    auto tmp = path;
    tmp += ".tmp";
    errno = 0;
    std::ofstream out(tmp, std::ios::binary | std::ios::trunc);
    if (!out) { const int code = errno; throw stream_error("Cannot open temporary output", tmp, code); }
    errno = 0;
    out.write(payload.data(), std::streamsize(payload.size()));
    out.flush();
    if (!out) { const int code = errno; throw stream_error("Cannot write temporary output", tmp, code); }
    errno = 0;
    out.close();
    if (!out) { const int code = errno; throw stream_error("Cannot close temporary output", tmp, code); }
#ifdef _WIN32
    // An external reader without FILE_SHARE_DELETE can temporarily prevent a
    // rename. Retry the rename only: never delete the committed checkpoint or
    // rewrite the temporary file while waiting for the reader to release it.
    const auto began = std::chrono::steady_clock::now();
    const auto deadline = began + std::chrono::seconds(5);
    auto delay = std::chrono::milliseconds(25);
    unsigned attempts = 0;
    for (;;) {
        ++attempts;
        if (MoveFileExW(tmp.c_str(), path.c_str(), MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH)) return;
        const DWORD code = GetLastError(); // Must precede all formatting and other API calls.
        const auto now = std::chrono::steady_clock::now();
        if (!retryable_replace_error(code) || now >= deadline) {
            const auto waited = std::chrono::duration_cast<std::chrono::milliseconds>(now - began).count();
            throw std::runtime_error("Atomic replace failed for " + display_path(path) + "; " + windows_error(code) +
                "; attempts=" + std::to_string(attempts) + "; elapsed_ms=" + std::to_string(waited) +
                ". Existing checkpoint was not deleted. Temporary output retained at " + display_path(tmp) +
                ". Resume uses the last committed .json checkpoint; .tmp is not recovered automatically.");
        }
        std::this_thread::sleep_until(std::min(deadline, now + delay));
        delay = std::min(delay * 2, std::chrono::milliseconds(250));
    }
#else
    if (std::rename(tmp.c_str(), path.c_str()) != 0) {
        const int code = errno;
        throw std::runtime_error("Atomic replace failed for " + display_path(path) + "; " +
            filesystem_error(std::error_code(code, std::generic_category())) +
            ". Existing checkpoint was not deleted. Temporary output retained at " + display_path(tmp));
    }
#endif
}

struct DirLock {
    fs::path path;
    explicit DirLock(fs::path p) : path(std::move(p)) {
        std::error_code ec;
        const bool created = fs::create_directory(path, ec);
        if (!created && (!ec || ec == std::errc::file_exists))
            throw std::runtime_error("Lock exists: " + display_path(path) +
                ". Remove only after confirming the previous process has stopped.");
        if (ec || !created)
            throw std::runtime_error("Cannot create lock directory " + display_path(path) + "; " + filesystem_error(ec));
    }
    ~DirLock() { std::error_code ec; fs::remove(path, ec); }
    DirLock(const DirLock&) = delete;
    DirLock& operator=(const DirLock&) = delete;
};
} // namespace fan_io
