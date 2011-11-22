/**
 * This file is part of CamImportPlugins/SotonImportPlugins.
 * 
 * Copyright (C) 2011 intranda GmbH
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * @author Andrey Kozhushkov
 */
package de.intranda.goobi.plugins;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.StringReader;
import java.io.StringWriter;
import java.io.UnsupportedEncodingException;
import java.net.URL;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.xeoh.plugins.base.annotations.PluginImplementation;

import org.apache.commons.httpclient.HttpClient;
import org.apache.commons.httpclient.HttpStatus;
import org.apache.commons.httpclient.methods.GetMethod;
import org.apache.commons.io.IOUtils;
import org.apache.commons.lang.StringUtils;
import org.apache.log4j.Logger;
import org.goobi.production.Import.Record;
import org.goobi.production.enums.ImportReturnValue;
import org.goobi.production.enums.ImportType;
import org.goobi.production.enums.PluginType;
import org.goobi.production.plugin.interfaces.IImportPlugin;
import org.goobi.production.plugin.interfaces.IPlugin;
import org.jdom.Namespace;
import org.jdom.Document;
import org.jdom.Element;
import org.jdom.JDOMException;
import org.jdom.input.SAXBuilder;
import org.jdom.output.Format;
import org.jdom.output.XMLOutputter;
import org.jdom.transform.XSLTransformer;

import ugh.dl.DigitalDocument;
import ugh.dl.DocStruct;
import ugh.dl.Fileformat;
import ugh.dl.Metadata;
import ugh.dl.MetadataType;
import ugh.dl.Prefs;
import ugh.exceptions.DocStructHasNoTypeException;
import ugh.exceptions.MetadataTypeNotAllowedException;
import ugh.exceptions.PreferencesException;
import ugh.exceptions.TypeNotAllowedForParentException;
import ugh.exceptions.WriteException;
import ugh.fileformats.mets.MetsMods;
import de.intranda.goobi.plugins.utils.ModsUtils;
import de.sub.goobi.Import.ImportOpac;
import de.sub.goobi.config.ConfigMain;

@PluginImplementation
public class CSICMixedImport implements IImportPlugin, IPlugin {

	/** Logger for this class. */
	private static final Logger logger = Logger
			.getLogger(CSICMixedImport.class);

	private static final String NAME = "CSICMixedImport";
	private static final String VERSION = "0.0.10000000";
	// private static final String XSLT_PATH = "jar:file:/" +
	// ConfigMain.getParameter("pluginFolder")
	// + "import/SotonImportPlugins.jar!/resources/MARC21slim2MODS3.xsl";
	private static final String XSLT_PATH = ConfigMain
			.getParameter("xsltFolder") + "MARC21slim2MODS3.xsl";
	private static final String MODS_MAPPING_FILE = ConfigMain
			.getParameter("xsltFolder") + "mods_map.xml";

	// Namespaces
	private Namespace mets;
	private Namespace premis;
	private Namespace mix;
	private Namespace marc;

	private Prefs prefs;
	private String data = "";
	private File importFile = null;
	private String importFolder = "output/";
	private Map<String, String> map = new HashMap<String, String>();
	private String currentIdentifier;
	private String currentTitle;
	private String currentAuthor;
	private List<String> currentCollectionList;
	private String encoding = "utf-8";

	private File exportFolder = new File("samples/0008_PCTN");

	public CSICMixedImport() {
		map.put("?monographic", "Monograph");
		map.put("?continuing", "Periodical");
		map.put("?multipart monograph", "MultiVolumeWork");
		map.put("?single unit", "Monograph");
		map.put("?integrating resource", "MultiVolumeWork");
		map.put("?serial", "Periodical");
		map.put("?cartographic", "Map");
		map.put("?notated music", null);
		map.put("?sound recording-nonmusical", null);
		map.put("?sound recording-musical", null);
		map.put("?moving image", null);
		map.put("?three dimensional object", null);
		map.put("?software, multimedia", null);
		map.put("?mixed material", null);
	}

	public static Element setNamespaceRecursive(Element root, Namespace ns) {
		List<Element> current = new ArrayList<Element>();
		current.add(root);
		do {
			List<Element> children = new ArrayList<Element>();
			for (Element element : current) {
				element.setNamespace(ns);
				children.addAll(element.getChildren());
			}
			current = children;
		} while (!current.isEmpty());

		return root;
	}

	public Fileformat convertData(String inString) {
		Fileformat ff = null;
		Document doc;
		try {
			doc = new SAXBuilder().build(new StringReader(inString));
			// doc = new SAXBuilder().build(new File("test.xml"));

			// remove namespaces
			Element docRoot = doc.getRootElement();
			docRoot = setNamespaceRecursive(docRoot, null);
			Element newRecord = new Element("record");
			List<Element> eleList = new ArrayList<Element>();
			for (Object obj : docRoot.getChildren()) {
				Element child = (Element) obj;
				eleList.add(child);
			}
			for (Element element : eleList) {
				element.detach();
			}
			newRecord.setContent(eleList);
			for (Object obj : newRecord.getChildren()) {
				Element child = (Element) obj;
				child.setNamespace(null);
			}
			docRoot.detach();
			doc.setRootElement(newRecord);

			logger.debug(new XMLOutputter().outputString(doc));
			if (doc != null && doc.hasRootElement()) {
				XSLTransformer transformer = new XSLTransformer(XSLT_PATH);
				// InputStream in =
				// getClass().getResourceAsStream("/MARC21slim2MODS3.xsl");
				// XSLTransformer transformer = new XSLTransformer(in);
				// in.close();
				Document docMods = transformer.transform(doc);

				logger.debug(new XMLOutputter().outputString(docMods));
				ff = new MetsMods(prefs);
				DigitalDocument dd = new DigitalDocument();
				ff.setDigitalDocument(dd);

				Element eleMods = docMods.getRootElement();
				if (eleMods.getName().equals("modsCollection")) {
					eleMods = eleMods.getChild("mods", null);
				}

				// Determine the root docstruct type
				String dsType = "Monograph";
				if (eleMods.getChild("originInfo", null) != null) {
					Element eleIssuance = eleMods.getChild("originInfo", null)
							.getChild("issuance", null);
					if (eleIssuance != null
							&& map.get("?" + eleIssuance.getTextTrim()) != null) {
						dsType = map.get("?" + eleIssuance.getTextTrim());
					}
				}
				Element eleTypeOfResource = eleMods.getChild("typeOfResource",
						null);
				if (eleTypeOfResource != null
						&& map.get("?" + eleTypeOfResource.getTextTrim()) != null) {
					dsType = map.get("?" + eleTypeOfResource.getTextTrim());
				}
				logger.debug("Docstruct type: " + dsType);

				DocStruct dsRoot = dd.createDocStruct(prefs
						.getDocStrctTypeByName(dsType));
				dd.setLogicalDocStruct(dsRoot);

				DocStruct dsBoundBook = dd.createDocStruct(prefs
						.getDocStrctTypeByName("BoundBook"));
				dd.setPhysicalDocStruct(dsBoundBook);
				// Collect MODS metadata
				ModsUtils.parseModsSection(MODS_MAPPING_FILE, prefs, dsRoot,
						dsBoundBook, eleMods);
				currentIdentifier = ModsUtils.getIdentifier(prefs, dsRoot);
				currentTitle = ModsUtils.getTitle(prefs, dsRoot);
				currentAuthor = ModsUtils.getAuthor(prefs, dsRoot);
				logger.debug("Author:" + currentAuthor + ", Title: "
						+ currentTitle);

				// Add 'pathimagefiles'
				try {
					Metadata mdForPath = new Metadata(
							prefs.getMetadataTypeByName("pathimagefiles"));
					mdForPath.setValue("./" + currentIdentifier);
					dsBoundBook.addMetadata(mdForPath);
				} catch (MetadataTypeNotAllowedException e1) {
					logger.error(
							"MetadataTypeNotAllowedException while reading images",
							e1);
				} catch (DocStructHasNoTypeException e1) {
					logger.error(
							"DocStructHasNoTypeException while reading images",
							e1);
				}

				// Add collection names attached to the current record
				if (currentCollectionList != null) {
					MetadataType mdTypeCollection = prefs
							.getMetadataTypeByName("singleDigCollection");
					for (String collection : currentCollectionList) {
						Metadata mdCollection = new Metadata(mdTypeCollection);
						mdCollection.setValue(collection);
						dsRoot.addMetadata(mdCollection);
					}
				}
			}
		} catch (JDOMException e) {
			logger.error(e.getMessage(), e);
		} catch (IOException e) {
			logger.error(e.getMessage(), e);
		} catch (PreferencesException e) {
			logger.error(e.getMessage(), e);
		} catch (TypeNotAllowedForParentException e) {
			logger.error(e.getMessage(), e);
		} catch (MetadataTypeNotAllowedException e) {
			logger.error(e.getMessage(), e);
		}

		return ff;
	}

	@Override
	public Fileformat convertData() {
		Fileformat ff = null;
		Document doc;
		try {
			doc = new SAXBuilder().build(new StringReader(data));
			// doc = new SAXBuilder().build(new File("test.xml"));

			// remove namespaces
			Element docRoot = doc.getRootElement();
			docRoot = setNamespaceRecursive(docRoot, null);
			Element newRecord = new Element("record");
			List<Element> eleList = new ArrayList<Element>();
			for (Object obj : docRoot.getChildren()) {
				Element child = (Element) obj;
				eleList.add(child);
			}
			for (Element element : eleList) {
				element.detach();
			}
			newRecord.setContent(eleList);
			for (Object obj : newRecord.getChildren()) {
				Element child = (Element) obj;
				child.setNamespace(null);
			}
			docRoot.detach();
			doc.setRootElement(newRecord);

			logger.debug(new XMLOutputter().outputString(doc));
			if (doc != null && doc.hasRootElement()) {
				XSLTransformer transformer = new XSLTransformer(XSLT_PATH);
				// InputStream in =
				// getClass().getResourceAsStream("/MARC21slim2MODS3.xsl");
				// XSLTransformer transformer = new XSLTransformer(in);
				// in.close();
				Document docMods = transformer.transform(doc);

				logger.debug(new XMLOutputter().outputString(docMods));
				ff = new MetsMods(prefs);
				DigitalDocument dd = new DigitalDocument();
				ff.setDigitalDocument(dd);

				Element eleMods = docMods.getRootElement();
				if (eleMods.getName().equals("modsCollection")) {
					eleMods = eleMods.getChild("mods", null);
				}

				// Determine the root docstruct type
				String dsType = "Monograph";
				if (eleMods.getChild("originInfo", null) != null) {
					Element eleIssuance = eleMods.getChild("originInfo", null)
							.getChild("issuance", null);
					if (eleIssuance != null
							&& map.get("?" + eleIssuance.getTextTrim()) != null) {
						dsType = map.get("?" + eleIssuance.getTextTrim());
					}
				}
				Element eleTypeOfResource = eleMods.getChild("typeOfResource",
						null);
				if (eleTypeOfResource != null
						&& map.get("?" + eleTypeOfResource.getTextTrim()) != null) {
					dsType = map.get("?" + eleTypeOfResource.getTextTrim());
				}
				logger.debug("Docstruct type: " + dsType);

				DocStruct dsRoot = dd.createDocStruct(prefs
						.getDocStrctTypeByName(dsType));
				dd.setLogicalDocStruct(dsRoot);

				DocStruct dsBoundBook = dd.createDocStruct(prefs
						.getDocStrctTypeByName("BoundBook"));
				dd.setPhysicalDocStruct(dsBoundBook);
				// Collect MODS metadata
				ModsUtils.parseModsSection(MODS_MAPPING_FILE, prefs, dsRoot,
						dsBoundBook, eleMods);
				currentIdentifier = ModsUtils.getIdentifier(prefs, dsRoot);
				currentTitle = ModsUtils.getTitle(prefs, dsRoot);
				currentAuthor = ModsUtils.getAuthor(prefs, dsRoot);
				logger.debug("Author:" + currentAuthor + ", Title: "
						+ currentTitle);

				// Add 'pathimagefiles'
				try {
					Metadata mdForPath = new Metadata(
							prefs.getMetadataTypeByName("pathimagefiles"));
					mdForPath.setValue("./" + currentIdentifier);
					dsBoundBook.addMetadata(mdForPath);
				} catch (MetadataTypeNotAllowedException e1) {
					logger.error(
							"MetadataTypeNotAllowedException while reading images",
							e1);
				} catch (DocStructHasNoTypeException e1) {
					logger.error(
							"DocStructHasNoTypeException while reading images",
							e1);
				}

				// Add collection names attached to the current record
				if (currentCollectionList != null) {
					MetadataType mdTypeCollection = prefs
							.getMetadataTypeByName("singleDigCollection");
					for (String collection : currentCollectionList) {
						Metadata mdCollection = new Metadata(mdTypeCollection);
						mdCollection.setValue(collection);
						dsRoot.addMetadata(mdCollection);
					}
				}
			}
		} catch (JDOMException e) {
			logger.error(e.getMessage(), e);
		} catch (IOException e) {
			logger.error(e.getMessage(), e);
		} catch (PreferencesException e) {
			logger.error(e.getMessage(), e);
		} catch (TypeNotAllowedForParentException e) {
			logger.error(e.getMessage(), e);
		} catch (MetadataTypeNotAllowedException e) {
			logger.error(e.getMessage(), e);
		}

		return ff;
	}

	@Override
	public HashMap<String, ImportReturnValue> generateFiles(List<Record> records) {
		HashMap<String, ImportReturnValue> ret = new HashMap<String, ImportReturnValue>();

		int i = 0;
		for (Record record : records) {
			logger.info("parsing record " + ++i);
			data = record.getData();
			Document doc = convertDocument();
			logger.info("converted document " + getProcessTitle());
			if (doc != null) {
				try {
					File hotFile = new File(importFolder, getProcessTitle());
					logger.debug("Writing '" + hotFile.getAbsolutePath() + "' into hotfolder...");
					getFileFromDocument(hotFile, doc);
					logger.debug("copying image files...");
					copyImageFiles(exportFolder);
					ret.put(getProcessTitle(), ImportReturnValue.ExportFinished);
				} catch (IOException e) {
					logger.error(e.getMessage(), e);
					ret.put(getProcessTitle(), ImportReturnValue.WriteError);
				}
			} else {
				ret.put(getProcessTitle(), ImportReturnValue.InvalidData);
			}
		}

		return ret;
	}

	@Override
	public List<Record> generateRecordsFromFile() {
		List<Record> ret = new ArrayList<Record>();
		InputStream input = null;
		StringWriter writer = null;
		try {
			logger.debug("loaded file: " + importFile.getAbsolutePath());
			input = new FileInputStream(importFile);
			Record record = new Record();
			writer = new StringWriter();
			IOUtils.copy(input, writer, encoding);
			record.setData(writer.toString());
			ret.add(record);

		} catch (FileNotFoundException e) {
			logger.error(e.getMessage(), e);
		} catch (IOException e) {
			logger.error(e.getMessage(), e);
		} finally {
			if (input != null) {
				try {
					if (writer != null)
						writer.close();
					input.close();
				} catch (IOException e) {
					logger.error(e.getMessage(), e);
				}
			}
			if (ret != null && importFile != null)
				logger.info("Extracted " + ret.size() + " records from '"
						+ importFile.getName() + "'.");
			else
				logger.error("No record extracted from importFile");
		}

		return ret;
	}

	@Override
	public List<Record> splitRecords(String records) {
		List<Record> ret = new ArrayList<Record>();

		// Split strings
		List<String> recordStrings = new ArrayList<String>();
		BufferedReader inputStream = new BufferedReader(new StringReader(
				records));

		StringBuilder sb = new StringBuilder();
		String l;
		try {
			while ((l = inputStream.readLine()) != null) {
				if (l.length() > 0) {
					if (l.startsWith("=LDR")) {
						if (sb.length() > 0) {
							recordStrings.add(sb.toString());
						}
						sb = new StringBuilder();
					}
					sb.append(l + "\n");
				}
			}
			if (sb.length() > 0) {
				recordStrings.add(sb.toString());
			}
		} catch (IOException e) {
			logger.error(e.getMessage(), e);
		}

		// Convert strings to MARCXML records and add them to Record objects
		for (String s : recordStrings) {
			String data;
			try {
				data = convertTextToMarcXml(s);
				if (data != null) {
					Record rec = new Record();
					rec.setData(data);
					ret.add(rec);
				}
			} catch (IOException e) {
				logger.error(e.getMessage(), e);
			}
		}

		return ret;
	}

	@Override
	public List<String> splitIds(String ids) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getProcessTitle() {
		if (StringUtils.isNotBlank(currentTitle)) {
			return new ImportOpac().createAtstsl(currentTitle, currentAuthor)
					.toLowerCase() + "_" + currentIdentifier + ".xml";
		}
		return currentIdentifier + ".xml";
	}

	@Override
	public void setData(Record r) {
		this.data = r.getData();
	}

	@Override
	public String getImportFolder() {
		return importFolder;
	}

	@Override
	public void setImportFolder(String folder) {
		this.importFolder = folder;
	}

	@Override
	public void setFile(File importFile) {
		this.importFile = importFile;
	}

	@Override
	public void setPrefs(Prefs prefs) {
		this.prefs = prefs;

	}

	@Override
	public List<ImportType> getImportTypes() {
		List<ImportType> answer = new ArrayList<ImportType>();
		answer.add(ImportType.Record);
		answer.add(ImportType.FILE);

		return answer;
	}

	@Override
	public PluginType getType() {
		return PluginType.Import;
	}

	@Override
	public String getTitle() {
		return getDescription();
	}

	@Override
	public String getId() {
		return getDescription();
	}

	@Override
	public String getDescription() {
		return NAME + " v" + VERSION;
	}

	/**
	 * 
	 * @param text
	 * @return
	 * @throws IOException
	 */
	private String convertTextToMarcXml(String text) throws IOException {
		if (StringUtils.isNotEmpty(text)) {
			Document doc = new Document();
			text = text.replace((char) 0x1E, ' ');
			BufferedReader reader = new BufferedReader(new StringReader(text));
			Element eleRoot = new Element("collection");
			doc.setRootElement(eleRoot);
			Element eleRecord = new Element("record");
			eleRoot.addContent(eleRecord);
			String str;
			while ((str = reader.readLine()) != null) {
				if (str.toUpperCase().startsWith("=LDR")) {
					// Leader
					Element eleLeader = new Element("leader");
					eleLeader.setText(str.substring(7));
					eleRecord.addContent(eleLeader);
				} else if (str.length() > 2) {
					String tag = str.substring(1, 4);
					if (tag.startsWith("00") && str.length() > 6) {
						// Control field
						str = str.substring(6);
						Element eleControlField = new Element("controlfield");
						eleControlField.setAttribute("tag", tag);
						eleControlField.addContent(str);
						eleRecord.addContent(eleControlField);
					} else if (str.length() > 6) {
						// Data field
						String ind1 = str.substring(6, 7);
						String ind2 = str.substring(7, 8);
						str = str.substring(8);
						Element eleDataField = new Element("datafield");
						eleDataField.setAttribute("tag", tag);
						eleDataField.setAttribute("ind1",
								!ind1.equals("\\") ? ind1 : "");
						eleDataField.setAttribute("ind2",
								!ind2.equals("\\") ? ind2 : "");
						Pattern p = Pattern.compile("[$]+[^$]+");
						Matcher m = p.matcher(str);
						while (m.find()) {
							String sub = str.substring(m.start(), m.end());
							Element eleSubField = new Element("subfield");
							eleSubField.setAttribute("code",
									sub.substring(1, 2));
							eleSubField.addContent(sub.substring(2));
							eleDataField.addContent(eleSubField);
						}
						eleRecord.addContent(eleDataField);
					}
				}
			}
			return new XMLOutputter().outputString(doc);
		}

		return null;
	}

	private Document getMarcDocument(Document inDoc) {
		Element marcRecord = null;

		// getting document elements
		Element root = inDoc.getRootElement();

		Element header = root.getChild("metsHdr", mets);
		logger.debug("getting document elements");
		if (root != null) {
			if (root.getChildren().isEmpty())
				logger.warn("No children found in root");
			else {
				marcRecord = root.getChild("dmdSec", mets)
						.getChild("mdWrap", mets).getChild("xmlData", mets)
						.getChild("marc", marc).getChild("record", marc);
				logger.debug("Name of marcRecord = " + (marcRecord == null ? "null"
						: marcRecord.getName()));
			}
		} else
			logger.warn("Root element not found");
		marcRecord.detach();
		return new Document(marcRecord);
	}

	private void getNamespaces(Element root) {
		mets = root.getNamespace("mets");
		logger.debug("Namespace mets: Prefix = " + mets.getPrefix()
				+ ", uri = " + mets.getURI());
		premis = root.getNamespace("premis");
		logger.debug("Namespace premis: Prefix = " + premis.getPrefix()
				+ ", uri = " + premis.getURI());
		mix = root.getNamespace("mix");
		logger.debug("Namespace mix: Prefix = " + mix.getPrefix() + ", uri = "
				+ mix.getURI());
		marc = root.getNamespace("marc");
		logger.debug("Namespace marc: Prefix = " + marc.getPrefix()
				+ ", uri = " + marc.getURI());
	}

	/**
	 * 
	 * Creates a single String out of the Document document
	 * 
	 * @param document
	 * @param encoding
	 * @return
	 */
	private String getStringFromDocument(Document document, String encoding) {
		if (document == null) {
			logger.warn("Trying to convert null document to String. Aborting");
			return null;
		}
		XMLOutputter outputter = new XMLOutputter();
		Format xmlFormat = outputter.getFormat();
		if (!(encoding == null) && !encoding.isEmpty())
			xmlFormat.setEncoding(encoding);
		xmlFormat.setExpandEmptyElements(true);
		outputter.setFormat(xmlFormat);
		String docString = outputter.outputString(document);

		return docString;
	}

	private Document getDocumentFromFile(File file) {
		SAXBuilder builder = new SAXBuilder(false);
		Document document = null;

		try {
			document = builder.build(file);
		} catch (JDOMException e) {
			logger.error(e.toString(), e);
			return null;
		} catch (IOException e) {
			logger.error(e.toString(), e);
			return null;
		}
		return document;
	}

	private Document getDocumentFromString(String string) {
		byte[] byteArray = null;
		try {
			byteArray = string.getBytes(encoding);
		} catch (UnsupportedEncodingException e1) {
		}
		ByteArrayInputStream baos = new ByteArrayInputStream(byteArray);

		// Reader reader = new StringReader(hOCRText);
		SAXBuilder builder = new SAXBuilder(false);
		Document document = null;

		try {
			document = builder.build(baos);
		} catch (JDOMException e) {
			System.err.println("error " + e.toString());
			return null;
		} catch (IOException e) {
			System.err.println(e.toString());
			return null;
		}
		return document;
	}

	private String getLogicalType(Document doc) {
		List<Element> structMaps = doc.getRootElement().getChildren(
				"structMap", mets);
		String type = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL")) {
				type = element.getChild("div", mets).getAttributeValue("TYPE");
				logger.debug("Found logical root type in marc document: "
						+ type);
			}
		}
		return type;
	}

	private String getPhysicalType(Document doc) {
		List<Element> structMaps = doc.getRootElement().getChildren(
				"structMap", mets);
		String type = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL")) {
				type = element.getChild("div", mets).getAttributeValue("TYPE");
				logger.debug("Found physical root type in marc document: "
						+ type);
			}
		}
		return type;
	}

	private Document convertDocument() {
		if (data == null || data.isEmpty()) {
			logger.warn("Attempting to convert empty data. Aborting.");
			return null;
		}
		Document modsDoc = null;
		Document marcDoc = null;
		Document doc = null;
		try {
			doc = getDocumentFromString(data);
			getNamespaces(doc.getRootElement());
			marcDoc = getMarcDocument(doc);
			String marcString = getStringFromDocument(marcDoc, encoding);
			Fileformat ff = convertData(marcString);
			if(ff!=null)
				ff.write("tempDoc.xml");
			modsDoc = getDocumentFromFile(new File("tempDoc.xml"));

		} catch (WriteException e) {
			logger.error(e.toString(), e);
		} catch (PreferencesException e) {
			logger.error(e.toString(), e);
		}

		doc = replaceXmlData(doc, modsDoc);
		doc = exchangeStructData(doc);
		doc = replaceStructData(doc, modsDoc);

//		logger.info("writing output file");
//		File outputFile = new File("output/finalOutput.xml");
//		getFileFromDocument(outputFile, doc);
		
		return doc;
	}

	private void getFileFromDocument(File file, Document doc) throws IOException {
		writeTextFile(getStringFromDocument(doc, encoding), file);
	}

	private void copyImageFiles(File exportFolder) {

		String id = currentIdentifier.replace("CSIC", "");

		List<File> folders = Arrays.asList(exportFolder.listFiles());
		List<File> imageFiles = null;
		File tiffDir = null, jpegDir = null, imageDir = null;
		for (File file : folders) {
			if (file.isDirectory() && file.getName().contentEquals("Tiff")) {
				logger.debug("found \"tiff\" directory in "
						+ exportFolder.getName());
				tiffDir = file;
			}
			if (file.isDirectory() && file.getName().contentEquals("JPG")) {
				logger.debug("found \"jpeg\" directory in "
						+ exportFolder.getName());
				jpegDir = file;
			}
		}

		// with no tiff dir, we assume the process directories are directly
		// within exportFolder
		if (tiffDir == null) {
			for (File folder : folders) {
				if (folder.isDirectory() && folder.getName().contains(id))
					imageDir = folder;
				logger.debug("found export folder " + imageDir + " in "
						+ exportFolder);
			}
		} else {
			// search in tiff-dir
			folders = Arrays.asList(tiffDir.listFiles());
			for (File folder : folders) {
				if (folder.isDirectory() && folder.getName().contains(id))
					imageDir = folder;
			}
			// if tiff-dir is empty or non-existant, search again in jpg dir
			if (imageDir == null || imageDir.listFiles() == null
					|| imageDir.listFiles().length == 0) {
				folders = Arrays.asList(jpegDir.listFiles());
				for (File folder : folders) {
					if (folder.isDirectory() && folder.getName().contains(id))
						imageDir = folder;
					logger.debug("found export folder " + imageDir + " in "
							+ jpegDir);
				}
			} else {
				logger.debug("found export folder " + imageDir + " in "
						+ tiffDir);
			}
		}

		// check if we have an image Dir now
		if (imageDir == null || imageDir.listFiles() == null
				|| imageDir.listFiles().length == 0) {
			logger.warn("No image dir found. Aborting image file import");
			return;
		}

		// get temp dir
		File tempDir = new File(importFolder, getProcessTitle().replace(".xml",
				""));
		tempDir.mkdir();
		List<File> images = Arrays.asList(imageDir.listFiles(ImageFilter));
		for (File imageFile : images) {
			try {
				InputStream inStream = new FileInputStream(imageFile);
				BufferedInputStream bis = new BufferedInputStream(inStream);
				String filename = imageFile.getName();
				FileOutputStream fos = new FileOutputStream(new File(tempDir,
						filename));
				byte[] bytes = new byte[8192];
				int count = bis.read(bytes);
				while (count != -1 && count <= 8192) {
					fos.write(bytes, 0, count);
					count = bis.read(bytes);
				}
				if (count != -1) {
					fos.write(bytes, 0, count);
				}
				fos.close();
				bis.close();
			} catch (Exception e) {
				logger.error(e.getMessage(), e);
			}
		}
	}

	public static File writeTextFile(String string, File file) throws IOException {

		FileWriter writer = null;
			writer = new FileWriter(file);
			writer.write(string);
			if (writer != null)
				writer.close();

		return file;
	}

	/**
	 * 
	 * makes the physical structMap of doc compatible with goobi
	 * 
	 * @param doc
	 * @param modsDoc
	 * @return
	 */
	private Document replaceStructData(Document doc, Document modsDoc) {

		Element physStruct = null, logStruct = null;
		List<Element> structMaps = doc.getRootElement().getChildren(
				"structMap", mets);

		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL"))
				physStruct = element;
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL"))
				logStruct = element;
		}

		// set type of logical root
		Element logRoot = null;
		for (Object obj : logStruct.getChildren("div", mets)) {
			if (obj instanceof Element)
				logRoot = (Element) obj;
			else
				break;

			logRoot.setAttribute("TYPE", getLogicalType(modsDoc));
		}

		// set type of physical root
		Element physRoot = null;
		for (Object obj : physStruct.getChildren("div", mets)) {
			if (obj instanceof Element)
				physRoot = (Element) obj;
			else
				break;

			physRoot.setAttribute("TYPE", getPhysicalType(modsDoc));
		}

		// remove "volume"
		List<Element> volumes = physRoot.getChildren();
		List<Element> volumeChildren = new ArrayList<Element>();
		int noVolumes = 0;
		for (Element volume : volumes) {
			if (volume.getAttributeValue("TYPE").contentEquals("VOLUME")) {
				volumeChildren.addAll(volume.cloneContent());
				noVolumes++;
			} else {
				volumeChildren.add(volume);
			}
		}
		if (noVolumes > 1)
			logger.warn("Number of volumes in book is " + noVolumes);
		physRoot.setContent(volumeChildren);

		// rename PAGE->page
		Iterator descendant = physRoot.getDescendants();
		while (descendant.hasNext()) {
			Element ele = null;
			Object obj = descendant.next();
			if (obj instanceof Element) {
				ele = (Element) obj;
				String value = ele.getAttributeValue("TYPE");
				if (value != null && value.contentEquals("PAGE"))
					ele.setAttribute("TYPE", "page");
			}

		}

		return doc;
	}

	/**
	 * Puts the logical StructData before physical StructData in the document
	 * structure of doc
	 * 
	 * @param doc
	 * @return
	 */
	private Document exchangeStructData(Document doc) {

		List<Element> structMaps = doc.getRootElement().getChildren(
				"structMap", mets);
		Element structLink = doc.getRootElement().getChild("structLink", mets);
		Element physStruct = null, logStruct = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL"))
				physStruct = element;
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL"))
				logStruct = element;
		}

		physStruct.detach();
		logStruct.detach();
		structLink.detach();

		doc.getRootElement().addContent(logStruct);
		doc.getRootElement().addContent(physStruct);
		doc.getRootElement().addContent(structLink);

		return doc;
	}

	/**
	 * 
	 * replaces the xmlData (actually the content of dmdSec) of doc with that of
	 * marcDoc
	 * 
	 * @param doc
	 * @param marcDoc
	 * @return
	 */
	private Document replaceXmlData(Document doc, Document marcDoc) {

		Element origDmdSec = doc.getRootElement().getChild("dmdSec", mets);
		Element newDmdSec = marcDoc.getRootElement().getChild("dmdSec", mets);

		origDmdSec.removeContent();
		origDmdSec.addContent(newDmdSec.cloneContent());

		return doc;
	}

	public static void main(String[] args) throws PreferencesException,
			WriteException {
		CSICMixedImport converter = new CSICMixedImport();
		converter.prefs = new Prefs();

		try {
			converter.prefs.loadPrefs("resources/ruleset1.xml");
		} catch (PreferencesException e) {
			logger.error(e.getMessage(), e);
		}

		converter.setImportFolder("output/");
		List<Record> records = new ArrayList<Record>();
		for (File file : converter.exportFolder.listFiles(XmlFilter)) {
			converter.setFile(file);
			records.addAll(converter.generateRecordsFromFile());
		}
		converter.generateFiles(records);
	}

	public static FilenameFilter ImageFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			// tif
			if (name.endsWith("tif") || name.endsWith("TIF")) {
				validImage = true;
			}

			// jpg
			if (name.endsWith("jpg") || name.endsWith("JPG")
					|| name.endsWith("jpeg") || name.endsWith("JPEG")) {
				validImage = true;
			}

			return validImage;
		}
	};
	
	public static FilenameFilter XmlFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("xml") || name.endsWith("XML")) {
				validImage = true;
			}

			return validImage;
		}
	};
}
