# Texas Rules and Standards Sync

This project is a Java/Maven command-line tool that syncs Texas court rules and standards PDFs (plus selected federal rules pages), tracks metadata, optionally emits text extracts, and can publish artifacts to local disk, SFTP, or WebDAV.

It can also be embedded and invoked from another Java application through `TexasRulesAndStandardsSync.runSync()`.

## What it does

- Crawls the Texas Courts rules/standards page and discovers linked documents.
- Downloads new or changed rule documents.
- Optionally keeps the previous version of each PDF when updates occur.
- Optionally builds combined PDFs:
  - `combined.pdf` (current set)
  - `combined_previous.pdf` (prior set, when previous retention is enabled)
- Extracts text artifacts from PDFs into `txt/`.
- Records synchronization metadata in `rules-standards-metadata.properties`.
- Optionally calls a webhook after successful downloads.

## Requirements

- Java 23
- Maven 3.9+

## Build

```bash
mvn clean package
```

The shaded runnable jar is produced at:

- `target/texasrulesandstandards-1.0-SNAPSHOT-fat.jar`

## Run

```bash
java -jar target/texasrulesandstandards-1.0-SNAPSHOT-fat.jar
```

### Embed in another Java application

```java
import group.chapmanlaw.texasrulesandstandards.TexasRulesAndStandardsSync;

int exitCode = TexasRulesAndStandardsSync.runSync();
```

`runSync()` returns:

- `0` for success
- `1` for execution failure
- `2` when no rule documents were discovered

You can also run with Maven:

```bash
mvn exec:java
```

## Configuration

Configuration can be supplied via either:

1. Java system properties (e.g., `-Dstorage.engine=sftp`), or
2. Environment variables (e.g., `STORAGE_ENGINE=sftp`)

System properties take precedence over environment variables.

### Core settings

| Purpose | Java property | Env var | Default |
|---|---|---|---|
| Storage backend (`local`, `sftp`, `webdav`) | `storage.engine` | `STORAGE_ENGINE` | `local` |
| Keep previous version of PDFs | `retain.previous.enabled` | `RETAIN_PREVIOUS_ENABLED` | `false` |
| Enable combined PDF generation | `combined.pdf.enabled` | `COMBINED_PDF_ENABLED` | `true` |
| Download webhook URL | `download.webhook.url` | `DOWNLOAD_WEBHOOK_URL` | disabled |
| Download webhook timeout (seconds) | `download.webhook.timeoutSeconds` | `DOWNLOAD_WEBHOOK_TIMEOUT_SECONDS` | `10` |

### SFTP settings (when `storage.engine=sftp`)

| Java property | Env var | Required | Default |
|---|---|---|---|
| `storage.sftp.host` | `SFTP_HOST` | Yes | — |
| `storage.sftp.port` | `SFTP_PORT` | No | `22` |
| `storage.sftp.username` | `SFTP_USERNAME` | Yes | — |
| `storage.sftp.password` | `SFTP_PASSWORD` | Yes | — |
| `storage.sftp.remoteDir` | `SFTP_REMOTE_DIR` | No | `/texas-rules-and-standards` |
| `storage.sftp.timeoutSeconds` | `SFTP_TIMEOUT_SECONDS` | No | `30` |

### WebDAV settings (when `storage.engine=webdav`)

| Java property | Env var | Required | Default |
|---|---|---|---|
| `storage.webdav.baseUrl` | `WEBDAV_BASE_URL` | Yes | — |
| `storage.webdav.username` | `WEBDAV_USERNAME` | Yes | — |
| `storage.webdav.password` | `WEBDAV_PASSWORD` | Yes | — |
| `storage.webdav.remoteDir` | `WEBDAV_REMOTE_DIR` | No | `/texas-rules-and-standards` |
| `storage.webdav.timeoutSeconds` | `WEBDAV_TIMEOUT_SECONDS` | No | `30` |

## Output artifacts

Depending on settings and detected changes, the run will create/update artifacts such as:

- Individual PDFs for each rule/standard document
- Previous-version PDFs (if enabled)
- `combined.pdf`
- `combined_previous.pdf` (if enabled)
- Text extracts under `txt/`
- `rules-standards-metadata.properties`
- Rotating log files matching `rules-standards-*.log`

For local storage, artifacts are written under `texasrulesandstandards_data/`.

## Example

Run against SFTP storage with combined PDF generation enabled:

```bash
STORAGE_ENGINE=sftp \
SFTP_HOST=example.org \
SFTP_USERNAME=sync-user \
SFTP_PASSWORD=secret \
SFTP_REMOTE_DIR=/legal/texas-rules \
RETAIN_PREVIOUS_ENABLED=true \
COMBINED_PDF_ENABLED=true \
java -jar target/texasrulesandstandards-1.0-SNAPSHOT-fat.jar
```

## Notes

- This is a batch sync tool; repeated runs are expected.
- If no content changed, the tool reuses existing metadata/artifacts where possible.
