package group.chapmanlaw.texasrulesandstandards;

import com.jcraft.jsch.ChannelSftp;
import com.jcraft.jsch.JSch;
import com.jcraft.jsch.JSchException;
import com.jcraft.jsch.Session;
import com.jcraft.jsch.SftpException;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.time.Duration;
import java.time.Instant;
import java.time.LocalDate;
import java.time.ZoneId;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import org.jsoup.Jsoup;
import org.jsoup.nodes.Document;
import org.jsoup.nodes.Element;
import org.jsoup.nodes.Node;
import org.jsoup.nodes.TextNode;

public class app {

    private static final URI SOURCE_PAGE_URI = URI.create("https://www.txcourts.gov/rules-forms/rules-standards/");
    private static final Path DATA_DIRECTORY = Path.of("data");
    private static final Path METADATA_FILE = DATA_DIRECTORY.resolve("rules-standards-metadata.properties");
    private static final String LOG_FILE_PATTERN = DATA_DIRECTORY.resolve("rules-standards-%g.log").toString();
    private static final int LOG_FILE_LIMIT_BYTES = 1_048_576;
    private static final int LOG_FILE_ROTATION_COUNT = 5;
    private static final String RULES_SECTION_HEADING = "Statewide Rules";
    private static final String STANDARDS_SECTION_HEADING = "Statewide Standards";
    private static final String STORAGE_ENGINE_LOCAL = "local";
    private static final String STORAGE_ENGINE_SFTP = "sftp";
    private static final Set<String> DOCUMENT_EXTENSIONS = Set.of("pdf", "doc", "docx");
    private static final String HTTP_USER_AGENT = "texas-rules-and-standards-sync/1.0 (+https://www.txcourts.gov/)";
    private static final Pattern DATE_PATTERN = Pattern.compile(
            "(?i)(January|February|March|April|May|June|July|August|September|October|November|December)\\s+\\d{1,2},\\s+\\d{4}");
    private static final Pattern HTML_ANCHOR_PATTERN = Pattern.compile(
            "<a\\b[^>]*href\\s*=\\s*['\"]([^'\"]+)['\"][^>]*>(.*?)</a>",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
    private static final DateTimeFormatter LAST_AMENDED_FORMAT = DateTimeFormatter.ofPattern("MMMM d, uuuu", Locale.US);
    private static final Logger LOGGER = Logger.getLogger(app.class.getName());

    public static void main(String[] args) {
        try {
            Files.createDirectories(DATA_DIRECTORY);
            configureLogging();

            LOGGER.info("Starting Texas rules and standards sync.");
            LOGGER.info("Source page: " + SOURCE_PAGE_URI);
            LOGGER.info("Data directory: " + DATA_DIRECTORY.toAbsolutePath());

            StorageSettings storageSettings = resolveStorageSettings();
            LOGGER.info("Configured storage engine: " + storageSettings.engine());
            if (STORAGE_ENGINE_SFTP.equals(storageSettings.engine())) {
                LOGGER.info("Configured SFTP endpoint: " + storageSettings.sftpEndpoint());
            }

            Properties previousMetadata = loadMetadata();
            LOGGER.info("Loaded metadata entries: " + countDocumentIds(previousMetadata));

            HttpClient httpClient = HttpClient.newBuilder()
                    .followRedirects(HttpClient.Redirect.NORMAL)
                    .connectTimeout(Duration.ofSeconds(30))
                    .build();

            String html = fetchHtml(httpClient, SOURCE_PAGE_URI);
            List<DocumentRecord> extractedDocuments = extractDocumentRecords(html, SOURCE_PAGE_URI);
            List<DocumentRecord> documents = deduplicateDocuments(extractedDocuments);

            if (documents.isEmpty()) {
                LOGGER.severe("No statewide rules/standards documents were found on the source page. The page format may have changed.");
                System.exit(2);
            }

            LOGGER.info("Discovered " + documents.size() + " candidate document(s) to track.");

            try (StorageEngine storageEngine = createStorageEngine(storageSettings)) {
                LOGGER.info("Active storage engine: " + storageEngine.name());
                LOGGER.info("Storage root: " + storageEngine.describeRoot());

                Properties updatedMetadata = new Properties();
                SyncStats stats = syncDocuments(httpClient, documents, previousMetadata, updatedMetadata, storageEngine);
                updatedMetadata.setProperty("storage.engine", storageEngine.name());
                updatedMetadata.setProperty("storage.root", storageEngine.describeRoot());
                writeMetadata(updatedMetadata);

                LOGGER.info("Sync completed.");
                LOGGER.info("Summary: downloaded=" + stats.downloaded()
                        + ", updated=" + stats.updated()
                        + ", skipped=" + stats.skipped()
                        + ", failed=" + stats.failed());
                LOGGER.info("Metadata written to " + METADATA_FILE.toAbsolutePath());
            }
        } catch (Exception ex) {
            LOGGER.log(Level.SEVERE, "Sync failed.", ex);
            System.exit(1);
        }
    }

    private static StorageSettings resolveStorageSettings() {
        String configuredEngine = normalizeStorageEngine(readConfig("storage.engine", "STORAGE_ENGINE", STORAGE_ENGINE_LOCAL));
        if (STORAGE_ENGINE_LOCAL.equals(configuredEngine)) {
            return StorageSettings.local();
        }
        if (!STORAGE_ENGINE_SFTP.equals(configuredEngine)) {
            throw new IllegalArgumentException(
                    "Unsupported storage engine '" + configuredEngine + "'. Supported values: local, sftp.");
        }

        String host = readRequiredConfig("storage.sftp.host", "SFTP_HOST");
        int port = parsePositiveInt(readConfig("storage.sftp.port", "SFTP_PORT", "22"), "storage.sftp.port/SFTP_PORT");
        String username = readRequiredConfig("storage.sftp.username", "SFTP_USERNAME");
        String password = readRequiredConfig("storage.sftp.password", "SFTP_PASSWORD");
        String remoteDirectory = normalizeRemoteDirectory(
                readConfig("storage.sftp.remoteDir", "SFTP_REMOTE_DIR", "/texas-rules-and-standards"));
        int timeoutSeconds = parsePositiveInt(
                readConfig("storage.sftp.timeoutSeconds", "SFTP_TIMEOUT_SECONDS", "30"),
                "storage.sftp.timeoutSeconds/SFTP_TIMEOUT_SECONDS");
        return new StorageSettings(configuredEngine, host, port, username, password, remoteDirectory, timeoutSeconds);
    }

    private static StorageEngine createStorageEngine(StorageSettings settings) throws IOException {
        if (STORAGE_ENGINE_SFTP.equals(settings.engine())) {
            return new SftpStorageEngine(settings);
        }
        return new LocalStorageEngine(DATA_DIRECTORY);
    }

    private static void configureLogging() throws IOException {
        LOGGER.setUseParentHandlers(false);
        LOGGER.setLevel(Level.INFO);

        for (Handler handler : LOGGER.getHandlers()) {
            LOGGER.removeHandler(handler);
            handler.close();
        }

        Formatter formatter = new SimpleLogFormatter();

        ConsoleHandler consoleHandler = new ConsoleHandler();
        consoleHandler.setLevel(Level.INFO);
        consoleHandler.setFormatter(formatter);
        LOGGER.addHandler(consoleHandler);

        FileHandler fileHandler = new FileHandler(LOG_FILE_PATTERN, LOG_FILE_LIMIT_BYTES, LOG_FILE_ROTATION_COUNT, true);
        fileHandler.setLevel(Level.ALL);
        fileHandler.setFormatter(formatter);
        LOGGER.addHandler(fileHandler);
    }

    private static Properties loadMetadata() throws IOException {
        Properties metadata = new Properties();
        if (!Files.exists(METADATA_FILE)) {
            return metadata;
        }

        String raw = Files.readString(METADATA_FILE, StandardCharsets.UTF_8);
        try (StringReader reader = new StringReader(raw)) {
            metadata.load(reader);
        }
        return metadata;
    }

    private static void writeMetadata(Properties metadata) throws IOException {
        StringWriter writer = new StringWriter();
        metadata.store(writer, "Texas rules and standards metadata");
        Files.writeString(
                METADATA_FILE,
                writer.toString(),
                StandardCharsets.UTF_8,
                StandardOpenOption.CREATE,
                StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE
        );
    }

    private static String fetchHtml(HttpClient httpClient, URI sourceUri) throws IOException, InterruptedException {
        LOGGER.info("Fetching source page HTML.");
        HttpRequest request = HttpRequest.newBuilder(sourceUri)
                .GET()
                .timeout(Duration.ofSeconds(45))
                .header("User-Agent", HTTP_USER_AGENT)
                .header("Accept", "text/html,application/xhtml+xml")
                .build();

        HttpResponse<String> response = httpClient.send(request, HttpResponse.BodyHandlers.ofString(StandardCharsets.UTF_8));
        int statusCode = response.statusCode();
        if (statusCode < 200 || statusCode >= 300) {
            throw new IOException("Failed to fetch source page. HTTP status " + statusCode);
        }

        LOGGER.info("Fetched source page HTML successfully (HTTP " + statusCode + ").");
        return response.body();
    }

    private static List<DocumentRecord> extractDocumentRecords(String html, URI sourcePage) {
        LOGGER.info("Extracting links and last amended dates from the page.");
        Document document = Jsoup.parse(html, sourcePage.toString());
        List<DocumentRecord> records = new ArrayList<>();

        records.addAll(extractSectionRecords(document, RULES_SECTION_HEADING, "rules"));
        records.addAll(extractSectionRecords(document, STANDARDS_SECTION_HEADING, "standards"));

        if (records.isEmpty()) {
            LOGGER.warning("Structured extraction returned no records. Trying HTML fallback extraction for CSS/JS markup changes.");
            records.addAll(extractFallbackRecordsFromRawHtml(html, sourcePage));
        }

        return records;
    }

    private static List<DocumentRecord> extractSectionRecords(Document document, String sectionHeading, String sectionKey) {
        Element heading = findHeadingByText(document, sectionHeading);
        if (heading == null) {
            LOGGER.warning("Could not find section heading: " + sectionHeading);
            return Collections.emptyList();
        }

        List<Element> sectionSiblings = collectSectionSiblings(heading);
        if (sectionSiblings.isEmpty()) {
            LOGGER.warning("No sibling content found after heading: " + sectionHeading);
            return Collections.emptyList();
        }

        List<SectionToken> tokens = new ArrayList<>();
        for (Element sibling : sectionSiblings) {
            collectSectionTokens(sibling, tokens);
        }

        List<DocumentRecord> records = new ArrayList<>();
        for (int i = 0; i < tokens.size(); i++) {
            SectionToken token = tokens.get(i);
            if (token.type() != TokenType.ANCHOR) {
                continue;
            }
            if (!looksLikeDocumentUrl(token.href())) {
                continue;
            }

            String title = normalizeWhitespace(token.text());
            if (title.isBlank()) {
                continue;
            }

            String lastAmended = findDateNearby(tokens, i);
            LocalDate lastAmendedDate = parseLastAmended(lastAmended);
            URI documentUri = resolveUri(SOURCE_PAGE_URI, token.href());
            if (documentUri == null) {
                LOGGER.warning("Skipping anchor with invalid URI: " + token.href());
                continue;
            }

            records.add(buildDocumentRecord(title, documentUri, sectionKey, lastAmended, lastAmendedDate));
        }

        LOGGER.info("Section '" + sectionHeading + "' yielded " + records.size() + " candidate document(s).");
        return records;
    }

    private static List<DocumentRecord> extractFallbackRecordsFromRawHtml(String html, URI sourcePage) {
        List<DocumentRecord> records = new ArrayList<>();
        String loweredHtml = html.toLowerCase(Locale.US);

        Matcher matcher = HTML_ANCHOR_PATTERN.matcher(html);
        while (matcher.find()) {
            String href = matcher.group(1);
            if (!looksLikeDocumentUrl(href)) {
                continue;
            }

            int contextStart = Math.max(0, matcher.start() - 2_500);
            String previousContext = loweredHtml.substring(contextStart, matcher.start());
            String sectionKey = inferSectionFromHtmlContext(previousContext);
            if (sectionKey == null) {
                continue;
            }

            String title = normalizeWhitespace(Jsoup.parse(matcher.group(2)).text());
            if (title.isBlank()) {
                continue;
            }

            int dateWindowEnd = Math.min(html.length(), matcher.end() + 450);
            String dateWindow = html.substring(matcher.start(), dateWindowEnd);
            String lastAmended = extractDateText(dateWindow);
            LocalDate lastAmendedDate = parseLastAmended(lastAmended);
            URI documentUri = resolveUri(sourcePage, href);
            if (documentUri == null) {
                continue;
            }

            records.add(buildDocumentRecord(title, documentUri, sectionKey, lastAmended, lastAmendedDate));
        }

        LOGGER.info("Fallback extraction yielded " + records.size() + " candidate document(s).");
        return records;
    }

    private static SyncStats syncDocuments(
            HttpClient httpClient,
            List<DocumentRecord> documents,
            Properties previousMetadata,
            Properties updatedMetadata,
            StorageEngine storageEngine
    ) throws IOException, InterruptedException {
        int downloaded = 0;
        int updated = 0;
        int skipped = 0;
        int failed = 0;

        Set<String> ids = new LinkedHashSet<>();
        for (DocumentRecord document : documents) {
            ids.add(document.id());
            LOGGER.info("Evaluating: " + document.title());
            LOGGER.info("  URL: " + document.downloadUri());
            LOGGER.info("  Last amended: " + (document.lastAmendedRaw() == null ? "Unknown" : document.lastAmendedRaw()));
            LOGGER.info("  Storage target: " + storageEngine.describeTarget(document));

            String metadataPrefix = "doc." + document.id() + ".";
            String previousLastAmended = previousMetadata.getProperty(metadataPrefix + "lastAmended");

            boolean storedCopyExists = storageEngine.exists(document);
            boolean shouldDownload;
            String reason;

            if (!storedCopyExists) {
                shouldDownload = true;
                reason = "missing stored file";
            } else if (previousLastAmended == null || previousLastAmended.isBlank()) {
                shouldDownload = true;
                reason = "existing file has no stored amendment date";
            } else if (isAmended(previousLastAmended, document.lastAmendedRaw(), document.lastAmended())) {
                shouldDownload = true;
                reason = "amendment date changed (stored: '" + previousLastAmended + "', current: '"
                        + safeValue(document.lastAmendedRaw()) + "')";
            } else {
                shouldDownload = false;
                reason = "no amendment change detected";
            }

            if (shouldDownload) {
                LOGGER.info("  Action: download+store (" + reason + ")");
                try {
                    boolean isUpdate = storedCopyExists;
                    byte[] bytes = downloadDocument(httpClient, document.downloadUri());
                    storageEngine.write(document, bytes);
                    downloaded++;
                    if (isUpdate) {
                        updated++;
                    }
                    LOGGER.info("  Result: download+store succeeded (" + bytes.length + " bytes)");
                    updateMetadataEntry(updatedMetadata, metadataPrefix, document, storageEngine);
                } catch (IOException | InterruptedException ex) {
                    failed++;
                    LOGGER.log(Level.SEVERE, "  Result: download+store failed for '" + document.title() + "'", ex);
                    preservePreviousMetadata(updatedMetadata, previousMetadata, metadataPrefix, document, storageEngine);
                    if (ex instanceof InterruptedException) {
                        Thread.currentThread().interrupt();
                        throw ex;
                    }
                }
            } else {
                skipped++;
                LOGGER.info("  Action: skip (" + reason + ")");
                updateMetadataEntry(updatedMetadata, metadataPrefix, document, storageEngine);
            }
        }

        updatedMetadata.setProperty("tracked.ids", String.join(",", ids));
        updatedMetadata.setProperty("tracked.count", Integer.toString(ids.size()));
        updatedMetadata.setProperty("source.page", SOURCE_PAGE_URI.toString());
        updatedMetadata.setProperty("source.lastCheckedAt", Instant.now().toString());

        return new SyncStats(downloaded, updated, skipped, failed);
    }

    private static byte[] downloadDocument(HttpClient httpClient, URI documentUri) throws IOException, InterruptedException {
        HttpRequest request = HttpRequest.newBuilder(documentUri)
                .GET()
                .timeout(Duration.ofSeconds(90))
                .header("User-Agent", HTTP_USER_AGENT)
                .header("Accept", "application/pdf,application/msword,application/vnd.openxmlformats-officedocument.wordprocessingml.document,*/*")
                .build();

        HttpResponse<byte[]> response = httpClient.send(request, HttpResponse.BodyHandlers.ofByteArray());
        int statusCode = response.statusCode();
        if (statusCode < 200 || statusCode >= 300) {
            throw new IOException("Download failed for " + documentUri + ". HTTP status " + statusCode);
        }

        byte[] body = response.body();
        if (body == null || body.length == 0) {
            throw new IOException("Download returned empty content for " + documentUri);
        }
        return body;
    }

    private static void updateMetadataEntry(
            Properties metadata,
            String metadataPrefix,
            DocumentRecord document,
            StorageEngine storageEngine
    ) {
        metadata.setProperty(metadataPrefix + "title", document.title());
        metadata.setProperty(metadataPrefix + "url", document.downloadUri().toString());
        metadata.setProperty(metadataPrefix + "section", document.sectionKey());
        metadata.setProperty(metadataPrefix + "fileName", document.fileName());
        metadata.setProperty(metadataPrefix + "storageEngine", storageEngine.name());
        metadata.setProperty(metadataPrefix + "storageTarget", storageEngine.describeTarget(document));
        metadata.setProperty(metadataPrefix + "lastAmended", safeValue(document.lastAmendedRaw()));
        metadata.setProperty(metadataPrefix + "lastSyncedAt", Instant.now().toString());
        metadata.remove(metadataPrefix + "lastAttemptFailedAt");
    }

    private static void preservePreviousMetadata(
            Properties updatedMetadata,
            Properties previousMetadata,
            String metadataPrefix,
            DocumentRecord document,
            StorageEngine storageEngine
    ) {
        boolean copied = false;
        for (String key : previousMetadata.stringPropertyNames()) {
            if (key.startsWith(metadataPrefix)) {
                updatedMetadata.setProperty(key, previousMetadata.getProperty(key, ""));
                copied = true;
            }
        }

        if (!copied) {
            updatedMetadata.setProperty(metadataPrefix + "title", document.title());
            updatedMetadata.setProperty(metadataPrefix + "url", document.downloadUri().toString());
            updatedMetadata.setProperty(metadataPrefix + "section", document.sectionKey());
            updatedMetadata.setProperty(metadataPrefix + "fileName", document.fileName());
            updatedMetadata.setProperty(metadataPrefix + "storageEngine", storageEngine.name());
            updatedMetadata.setProperty(metadataPrefix + "storageTarget", storageEngine.describeTarget(document));
            updatedMetadata.setProperty(metadataPrefix + "lastAmended", "");
        }

        updatedMetadata.setProperty(metadataPrefix + "lastAttemptFailedAt", Instant.now().toString());
    }

    private static Element findHeadingByText(Document document, String headingText) {
        for (Element heading : document.select("h1,h2,h3,h4,h5,h6")) {
            if (normalizeWhitespace(heading.text()).equalsIgnoreCase(headingText)) {
                return heading;
            }
        }
        return null;
    }

    private static List<Element> collectSectionSiblings(Element heading) {
        List<Element> sectionSiblings = new ArrayList<>();
        int headingLevel = headingLevel(heading);
        for (Element sibling = heading.nextElementSibling(); sibling != null; sibling = sibling.nextElementSibling()) {
            if (isBoundaryHeading(sibling, headingLevel)) {
                break;
            }
            sectionSiblings.add(sibling);
        }
        return sectionSiblings;
    }

    private static void collectSectionTokens(Node node, List<SectionToken> tokens) {
        if (node instanceof Element element) {
            if ("a".equalsIgnoreCase(element.tagName()) && element.hasAttr("href")) {
                String href = element.attr("href").trim();
                String text = normalizeWhitespace(element.text());
                if (!href.isBlank()) {
                    tokens.add(SectionToken.anchor(text, href));
                }
                return;
            }
        } else if (node instanceof TextNode textNode) {
            String text = normalizeWhitespace(textNode.text());
            if (!text.isBlank()) {
                tokens.add(SectionToken.text(text));
            }
            return;
        }

        for (Node child : node.childNodes()) {
            collectSectionTokens(child, tokens);
        }
    }

    private static boolean looksLikeDocumentUrl(String href) {
        if (href == null || href.isBlank()) {
            return false;
        }
        String lower = href.toLowerCase(Locale.US);
        for (String extension : DOCUMENT_EXTENSIONS) {
            if (lower.contains("." + extension)) {
                return true;
            }
        }
        return false;
    }

    private static String inferSectionFromHtmlContext(String loweredContext) {
        int rulesIndex = loweredContext.lastIndexOf(RULES_SECTION_HEADING.toLowerCase(Locale.US));
        int standardsIndex = loweredContext.lastIndexOf(STANDARDS_SECTION_HEADING.toLowerCase(Locale.US));
        if (rulesIndex < 0 && standardsIndex < 0) {
            return null;
        }
        return standardsIndex > rulesIndex ? "standards" : "rules";
    }

    private static String findDateNearby(List<SectionToken> tokens, int anchorIndex) {
        for (int i = anchorIndex + 1; i < tokens.size(); i++) {
            SectionToken token = tokens.get(i);
            if (token.type() == TokenType.ANCHOR) {
                break;
            }
            String date = extractDateText(token.text());
            if (date != null) {
                return date;
            }
        }

        for (int i = anchorIndex - 1; i >= 0; i--) {
            SectionToken token = tokens.get(i);
            if (token.type() == TokenType.ANCHOR) {
                break;
            }
            String date = extractDateText(token.text());
            if (date != null) {
                return date;
            }
        }

        return null;
    }

    private static String extractDateText(String text) {
        if (text == null || text.isBlank()) {
            return null;
        }
        Matcher matcher = DATE_PATTERN.matcher(text);
        if (!matcher.find()) {
            return null;
        }
        return normalizeWhitespace(matcher.group());
    }

    private static LocalDate parseLastAmended(String lastAmended) {
        if (lastAmended == null || lastAmended.isBlank()) {
            return null;
        }
        try {
            return LocalDate.parse(lastAmended.trim(), LAST_AMENDED_FORMAT);
        } catch (DateTimeParseException ignored) {
            return null;
        }
    }

    private static URI resolveUri(URI baseUri, String href) {
        try {
            return baseUri.resolve(href.trim());
        } catch (Exception ex) {
            LOGGER.warning("Unable to resolve URI '" + href + "': " + ex.getMessage());
            return null;
        }
    }

    private static DocumentRecord buildDocumentRecord(
            String title,
            URI documentUri,
            String sectionKey,
            String lastAmendedRaw,
            LocalDate lastAmended
    ) {
        String extension = determineExtension(documentUri);
        String id = toSlug(sectionKey + "-" + title);
        if (id.isBlank()) {
            id = sectionKey + "-document-" + Integer.toHexString(documentUri.toString().hashCode());
        }
        String fileName = id + "." + extension;
        return new DocumentRecord(
                id,
                normalizeWhitespace(title),
                documentUri,
                sectionKey,
                normalizeNullable(lastAmendedRaw),
                lastAmended,
                fileName
        );
    }

    private static String determineExtension(URI documentUri) {
        String path = documentUri.getPath();
        if (path == null) {
            return "pdf";
        }

        Matcher matcher = Pattern.compile("\\.([A-Za-z0-9]{2,5})$").matcher(path);
        if (!matcher.find()) {
            return "pdf";
        }

        String extension = matcher.group(1).toLowerCase(Locale.US);
        if (!DOCUMENT_EXTENSIONS.contains(extension)) {
            return "pdf";
        }
        return extension;
    }

    private static String toSlug(String value) {
        String normalized = value == null ? "" : value.toLowerCase(Locale.US);
        normalized = normalized.replaceAll("[^a-z0-9]+", "-");
        normalized = normalized.replaceAll("^-+", "");
        normalized = normalized.replaceAll("-+$", "");
        return normalized;
    }

    private static boolean isAmended(String previousRawDate, String currentRawDate, LocalDate currentDate) {
        if (currentRawDate == null || currentRawDate.isBlank()) {
            return false;
        }

        LocalDate previousDate = parseLastAmended(previousRawDate);
        if (previousDate != null && currentDate != null) {
            return !previousDate.equals(currentDate);
        }

        return !normalizeWhitespace(previousRawDate).equalsIgnoreCase(normalizeWhitespace(currentRawDate));
    }

    private static int headingLevel(Element element) {
        String tag = element.tagName().toLowerCase(Locale.US);
        if (tag.length() != 2 || tag.charAt(0) != 'h') {
            return 7;
        }
        char digit = tag.charAt(1);
        if (digit < '1' || digit > '6') {
            return 7;
        }
        return digit - '0';
    }

    private static boolean isBoundaryHeading(Element element, int startHeadingLevel) {
        int level = headingLevel(element);
        return level <= startHeadingLevel;
    }

    private static List<DocumentRecord> deduplicateDocuments(List<DocumentRecord> records) {
        Map<String, DocumentRecord> deduplicated = new LinkedHashMap<>();
        for (DocumentRecord record : records) {
            DocumentRecord existing = deduplicated.get(record.id());
            if (existing == null) {
                deduplicated.put(record.id(), record);
                continue;
            }
            if (existing.lastAmended() == null && record.lastAmended() != null) {
                deduplicated.put(record.id(), record);
            }
        }
        return new ArrayList<>(deduplicated.values());
    }

    private static int countDocumentIds(Properties metadata) {
        String trackedIds = metadata.getProperty("tracked.ids");
        if (trackedIds == null || trackedIds.isBlank()) {
            return 0;
        }
        String[] parts = trackedIds.split(",");
        int count = 0;
        for (String part : parts) {
            if (!part.isBlank()) {
                count++;
            }
        }
        return count;
    }

    private static String normalizeWhitespace(String value) {
        if (value == null) {
            return "";
        }
        return value.replaceAll("\\s+", " ").trim();
    }

    private static String normalizeNullable(String value) {
        String normalized = normalizeWhitespace(value);
        return normalized.isBlank() ? null : normalized;
    }

    private static String safeValue(String value) {
        return value == null ? "" : value;
    }

    private static String normalizeStorageEngine(String value) {
        if (value == null || value.isBlank()) {
            return STORAGE_ENGINE_LOCAL;
        }
        return value.trim().toLowerCase(Locale.US);
    }

    private static String readConfig(String propertyKey, String envKey, String defaultValue) {
        String propertyValue = System.getProperty(propertyKey);
        if (propertyValue != null && !propertyValue.isBlank()) {
            return propertyValue.trim();
        }
        String envValue = System.getenv(envKey);
        if (envValue != null && !envValue.isBlank()) {
            return envValue.trim();
        }
        return defaultValue;
    }

    private static String readRequiredConfig(String propertyKey, String envKey) {
        String value = readConfig(propertyKey, envKey, null);
        if (value == null || value.isBlank()) {
            throw new IllegalArgumentException(
                    "Missing required setting '" + propertyKey + "' (or environment variable '" + envKey + "').");
        }
        return value;
    }

    private static int parsePositiveInt(String rawValue, String settingLabel) {
        if (rawValue == null || rawValue.isBlank()) {
            throw new IllegalArgumentException("Setting '" + settingLabel + "' cannot be empty.");
        }
        try {
            int parsed = Integer.parseInt(rawValue.trim());
            if (parsed <= 0) {
                throw new IllegalArgumentException("Setting '" + settingLabel + "' must be greater than zero.");
            }
            return parsed;
        } catch (NumberFormatException ex) {
            throw new IllegalArgumentException("Setting '" + settingLabel + "' must be an integer. Got: " + rawValue, ex);
        }
    }

    private static String normalizeRemoteDirectory(String remoteDirectory) {
        if (remoteDirectory == null || remoteDirectory.isBlank()) {
            return "/";
        }
        String normalized = remoteDirectory.trim().replace('\\', '/');
        if (!normalized.startsWith("/")) {
            normalized = "/" + normalized;
        }
        normalized = normalized.replaceAll("/+", "/");
        if (normalized.length() > 1 && normalized.endsWith("/")) {
            normalized = normalized.substring(0, normalized.length() - 1);
        }
        return normalized;
    }

    private static boolean isNoSuchFileError(SftpException exception) {
        return exception.id == ChannelSftp.SSH_FX_NO_SUCH_FILE;
    }

    private interface StorageEngine extends AutoCloseable {

        String name();

        String describeRoot();

        String describeTarget(DocumentRecord document);

        boolean exists(DocumentRecord document) throws IOException;

        void write(DocumentRecord document, byte[] bytes) throws IOException;

        @Override
        default void close() throws IOException {
        }
    }

    private static final class LocalStorageEngine implements StorageEngine {

        private final Path rootDirectory;

        private LocalStorageEngine(Path rootDirectory) throws IOException {
            this.rootDirectory = rootDirectory;
            Files.createDirectories(rootDirectory);
        }

        @Override
        public String name() {
            return STORAGE_ENGINE_LOCAL;
        }

        @Override
        public String describeRoot() {
            return rootDirectory.toAbsolutePath().toString();
        }

        @Override
        public String describeTarget(DocumentRecord document) {
            return rootDirectory.resolve(document.fileName()).toAbsolutePath().toString();
        }

        @Override
        public boolean exists(DocumentRecord document) {
            return Files.exists(rootDirectory.resolve(document.fileName()));
        }

        @Override
        public void write(DocumentRecord document, byte[] bytes) throws IOException {
            Path destinationPath = rootDirectory.resolve(document.fileName());
            Path tempFile = Files.createTempFile(rootDirectory, "rules-standards-", ".tmp");
            try {
                Files.write(tempFile, bytes, StandardOpenOption.TRUNCATE_EXISTING);
                try {
                    Files.move(tempFile, destinationPath, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE);
                } catch (AtomicMoveNotSupportedException ignored) {
                    Files.move(tempFile, destinationPath, StandardCopyOption.REPLACE_EXISTING);
                }
            } finally {
                Files.deleteIfExists(tempFile);
            }
        }
    }

    private static final class SftpStorageEngine implements StorageEngine {

        private final StorageSettings settings;
        private final Session session;
        private final ChannelSftp channel;
        private final String remoteRoot;

        private SftpStorageEngine(StorageSettings settings) throws IOException {
            this.settings = settings;

            Session connectedSession = null;
            ChannelSftp connectedChannel = null;
            String connectedRemoteRoot = null;

            try {
                JSch jsch = new JSch();
                connectedSession = jsch.getSession(settings.sftpUsername(), settings.sftpHost(), settings.sftpPort());
                connectedSession.setPassword(settings.sftpPassword());

                Properties sessionConfig = new Properties();
                sessionConfig.setProperty("StrictHostKeyChecking", "no");
                connectedSession.setConfig(sessionConfig);
                int timeoutMillis = settings.sftpTimeoutSeconds() * 1_000;
                connectedSession.connect(timeoutMillis);

                connectedChannel = (ChannelSftp) connectedSession.openChannel("sftp");
                connectedChannel.connect(timeoutMillis);
                connectedRemoteRoot = ensureRemoteDirectory(connectedChannel, settings.sftpRemoteDir());
            } catch (JSchException | SftpException ex) {
                if (connectedChannel != null) {
                    connectedChannel.disconnect();
                }
                if (connectedSession != null) {
                    connectedSession.disconnect();
                }
                throw new IOException("Unable to initialize SFTP storage engine.", ex);
            }

            this.session = connectedSession;
            this.channel = connectedChannel;
            this.remoteRoot = connectedRemoteRoot;
        }

        @Override
        public String name() {
            return STORAGE_ENGINE_SFTP;
        }

        @Override
        public String describeRoot() {
            return settings.sftpEndpoint();
        }

        @Override
        public String describeTarget(DocumentRecord document) {
            return "sftp://" + settings.sftpHost() + ":" + settings.sftpPort() + remotePath(document.fileName());
        }

        @Override
        public boolean exists(DocumentRecord document) throws IOException {
            try {
                channel.lstat(remotePath(document.fileName()));
                return true;
            } catch (SftpException ex) {
                if (isNoSuchFileError(ex)) {
                    return false;
                }
                throw new IOException("Unable to check remote file existence.", ex);
            }
        }

        @Override
        public void write(DocumentRecord document, byte[] bytes) throws IOException {
            String targetPath = remotePath(document.fileName());
            String tempPath = targetPath + ".tmp-" + Instant.now().toEpochMilli();
            try (ByteArrayInputStream input = new ByteArrayInputStream(bytes)) {
                channel.put(input, tempPath, ChannelSftp.OVERWRITE);
                try {
                    channel.rm(targetPath);
                } catch (SftpException ex) {
                    if (!isNoSuchFileError(ex)) {
                        throw ex;
                    }
                }
                channel.rename(tempPath, targetPath);
            } catch (SftpException ex) {
                cleanupTempFile(tempPath);
                throw new IOException("Unable to write remote file '" + targetPath + "'.", ex);
            }
        }

        @Override
        public void close() {
            if (channel != null && channel.isConnected()) {
                channel.disconnect();
            }
            if (session != null && session.isConnected()) {
                session.disconnect();
            }
        }

        private String remotePath(String fileName) {
            if ("/".equals(remoteRoot)) {
                return "/" + fileName;
            }
            return remoteRoot + "/" + fileName;
        }

        private void cleanupTempFile(String tempPath) {
            try {
                channel.rm(tempPath);
            } catch (SftpException ignored) {
            }
        }

        private static String ensureRemoteDirectory(ChannelSftp channel, String remoteDirectory) throws SftpException {
            String normalized = normalizeRemoteDirectory(remoteDirectory);
            channel.cd("/");
            if ("/".equals(normalized)) {
                return normalized;
            }

            String[] parts = normalized.substring(1).split("/");
            for (String part : parts) {
                if (part.isBlank()) {
                    continue;
                }
                try {
                    channel.cd(part);
                } catch (SftpException ex) {
                    if (!isNoSuchFileError(ex)) {
                        throw ex;
                    }
                    channel.mkdir(part);
                    channel.cd(part);
                }
            }
            return normalized;
        }
    }

    private record SyncStats(int downloaded, int updated, int skipped, int failed) {
    }

    private record StorageSettings(
            String engine,
            String sftpHost,
            int sftpPort,
            String sftpUsername,
            String sftpPassword,
            String sftpRemoteDir,
            int sftpTimeoutSeconds
    ) {

        private static StorageSettings local() {
            return new StorageSettings(STORAGE_ENGINE_LOCAL, null, 22, null, null, "/", 30);
        }

        private String sftpEndpoint() {
            return "sftp://" + sftpHost + ":" + sftpPort + sftpRemoteDir;
        }
    }

    private record DocumentRecord(
            String id,
            String title,
            URI downloadUri,
            String sectionKey,
            String lastAmendedRaw,
            LocalDate lastAmended,
            String fileName
    ) {
    }

    private enum TokenType {
        ANCHOR,
        TEXT
    }

    private record SectionToken(TokenType type, String text, String href) {
        private static SectionToken anchor(String text, String href) {
            return new SectionToken(TokenType.ANCHOR, text, href);
        }

        private static SectionToken text(String text) {
            return new SectionToken(TokenType.TEXT, text, null);
        }
    }

    private static final class SimpleLogFormatter extends Formatter {

        @Override
        public String format(LogRecord record) {
            Instant instant = Instant.ofEpochMilli(record.getMillis());
            String timestamp = DateTimeFormatter.ofPattern("uuuu-MM-dd HH:mm:ss")
                    .withZone(ZoneId.systemDefault())
                    .format(instant);

            StringBuilder output = new StringBuilder();
            output.append(timestamp)
                    .append(" [")
                    .append(record.getLevel().getName())
                    .append("] ")
                    .append(formatMessage(record))
                    .append(System.lineSeparator());

            Throwable thrown = record.getThrown();
            if (thrown != null) {
                output.append("  cause: ").append(thrown).append(System.lineSeparator());
                for (StackTraceElement element : thrown.getStackTrace()) {
                    output.append("    at ").append(element).append(System.lineSeparator());
                }
            }
            return output.toString();
        }
    }
}
